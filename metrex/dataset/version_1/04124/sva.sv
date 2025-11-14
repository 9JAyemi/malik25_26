// SVA for top_module and accu (bind these to the DUT)

module top_sva_m(
  input clk,
  input reset,
  input [7:0] serial_input,
  input [7:0] serial_data,
  input [2:0] cycle_count,
  input average_valid
);
  default clocking cb @(posedge clk); endclocking

  // Reset values
  assert property (reset |=> (serial_data==8'h00 && cycle_count==3'b000));

  // serial_data samples serial_input
  assert property ((!reset && !$past(reset)) |-> (serial_data == $past(serial_input)));

  // Counter increments and wraps
  assert property ((!reset && !$past(reset)) |-> (cycle_count == $past(cycle_count)+3'b001));
  assert property (disable iff (reset) (cycle_count==3'b111) |=> (cycle_count==3'b000));

  // average_valid correctness and pulse width
  assert property (average_valid == (cycle_count==3'b111));
  assert property (disable iff (reset) average_valid |=> !average_valid);

  // Coverage
  cover property (disable iff (reset) $rose(average_valid));
  cover property (disable iff (reset) $rose(average_valid) ##8 $rose(average_valid));
endmodule

bind top_module top_sva_m top_sva_i(
  .clk(clk),
  .reset(reset),
  .serial_input(serial_input),
  .serial_data(serial_data),
  .cycle_count(cycle_count),
  .average_valid(average_valid)
);


// accu SVA

module accu_sva_m(
  input clk,
  input rst_n,
  input [7:0] data_in,
  input valid_a,
  input ready_b,
  input ready_a,
  input valid_b,
  input [9:0] data_out,
  input [9:0] accumulator,
  input [2:0] cycle_count
);
  default clocking cb @(posedge clk); endclocking

  // Async reset values at clock edge
  assert property (!rst_n |-> (accumulator==10'h000 && cycle_count==3'b000 && !ready_a && !valid_b));

  // Structural tie-off
  assert property (ready_b); // tied to 1'b1 in DUT

  // No handshake => state holds, outputs low
  assert property (disable iff (!rst_n) (!(valid_a && ready_b))
                   |-> $stable(accumulator) && $stable(cycle_count) && !ready_a && !valid_b);

  // Handshake, not last beat
  assert property (disable iff (!rst_n) (valid_a && ready_b && cycle_count!=3'b111)
                   |=> (accumulator == $past(accumulator)+data_in)
                    && (cycle_count == $past(cycle_count)+3'b001)
                    && !ready_a && !valid_b);

  // Handshake on last beat: flags, data_out, next-state resets
  assert property (disable iff (!rst_n) (valid_a && ready_b && cycle_count==3'b111)
                   |-> (ready_a && valid_b && (data_out == $past(accumulator)/6)));
  assert property (disable iff (!rst_n) (valid_a && ready_b && cycle_count==3'b111)
                   |=> (accumulator==10'h000 && cycle_count==3'b000));

  // valid_b/ready_a exact condition and pulse width
  assert property (disable iff (!rst_n) (valid_b == (valid_a && ready_b && cycle_count==3'b111)));
  assert property (disable iff (!rst_n) (ready_a == (valid_a && ready_b && cycle_count==3'b111)));
  assert property (disable iff (!rst_n) valid_b |=> !valid_b);

  // data_out changes only when valid_b
  assert property (disable iff (!rst_n) $changed(data_out) |-> valid_b);

  // Coverage
  cover property (disable iff (!rst_n) $rose(valid_b));
  cover property (disable iff (!rst_n) (valid_a && ready_b && cycle_count==3'b111) ##0 valid_b);
endmodule

bind accu accu_sva_m accu_sva_i(
  .clk(clk),
  .rst_n(rst_n),
  .data_in(data_in),
  .valid_a(valid_a),
  .ready_b(ready_b),
  .ready_a(ready_a),
  .valid_b(valid_b),
  .data_out(data_out),
  .accumulator(accumulator),
  .cycle_count(cycle_count)
);