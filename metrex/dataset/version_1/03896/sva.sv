// SVA checker for sensor_interface
module sensor_interface_sva #(
  parameter int clk_freq   = 100_000_000,
  parameter int sample_freq= 100,
  localparam int N = clk_freq / sample_freq
)(
  input  logic        clk,
  input  logic [7:0]  temp_data, pressure_data, humidity_data,
  input  logic        temp_ready, pressure_ready, humidity_ready,
  input  logic [7:0]  temp_out, pressure_out, humidity_out,
  input  logic [31:0] sample_counter
);

  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  initial past_valid = 0;
  always @(posedge clk) past_valid <= 1;

  // Counter safety and next-state relation
  assert property (sample_counter <= N);
  assert property (disable iff (!past_valid)
                   ($past(sample_counter) <  N) |-> (sample_counter == $past(sample_counter)+1));
  assert property (disable iff (!past_valid)
                   ($past(sample_counter) == N) |-> (sample_counter == 0));

  // Ready pulses only when sampling, one-cycle wide, all equal
  assert property ((sample_counter == N) |-> ##0 (temp_ready && pressure_ready && humidity_ready));
  assert property ((sample_counter != N) |-> ##0 (!temp_ready && !pressure_ready && !humidity_ready));
  assert property ((sample_counter == N) |-> ##1 (!temp_ready && !pressure_ready && !humidity_ready));
  assert property (temp_ready == pressure_ready && temp_ready == humidity_ready);

  // Data capture on sample event, hold otherwise
  assert property ((sample_counter == N) |-> ##0 (temp_out == temp_data
                                               && pressure_out == pressure_data
                                               && humidity_out == humidity_data));
  assert property (disable iff (!past_valid)
                   (sample_counter != N) |-> ##0 (temp_out == $past(temp_out)
                                               && pressure_out == $past(pressure_out)
                                               && humidity_out == $past(humidity_out)));

  // No unknowns on ready lines
  assert property (!$isunknown({temp_ready,pressure_ready,humidity_ready}));

  // Functional coverage
  cover property (sample_counter == N ##0 (temp_ready && pressure_ready && humidity_ready));
  cover property (disable iff (!past_valid)
                  ($past(sample_counter)==N, sample_counter==0) ##[1:$] (sample_counter==N));

endmodule

// Bind into DUT
bind sensor_interface sensor_interface_sva #(.clk_freq(clk_freq), .sample_freq(sample_freq)) u_sensor_interface_sva (
  .clk(clk),
  .temp_data(temp_data),
  .pressure_data(pressure_data),
  .humidity_data(humidity_data),
  .temp_ready(temp_ready),
  .pressure_ready(pressure_ready),
  .humidity_ready(humidity_ready),
  .temp_out(temp_out),
  .pressure_out(pressure_out),
  .humidity_out(humidity_out),
  .sample_counter(sample_counter)
);