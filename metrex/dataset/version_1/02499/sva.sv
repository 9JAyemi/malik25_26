// SVA for output_signal_module
module output_signal_module_sva (
  input        clk,
  input        reset,
  input [15:0] input_signal,
  input [3:0]  output_signal
);
  default clocking cb @(posedge clk); endclocking

  // Asynchronous reset takes effect immediately
  assert property (@(negedge reset) output_signal == 4'h0);

  // While reset is low, output must be 0 on every clock
  assert property ( !reset |-> output_signal == 4'h0 );

  // After reset deasserts (between clocks), hold 0 until next clk edge
  assert property ( $rose(reset) |-> (output_signal == 4'h0) until_with $rose(clk) );

  // Functional mapping: when out of reset, Q follows D (1-cycle observed check)
  assert property ( reset && $past(reset) |-> output_signal == $past(input_signal[15:12]) );

  // No spurious changes when input nibble is stable (out of reset)
  assert property ( reset && $past(reset) &&
                    (input_signal[15:12] == $past(input_signal[15:12]))
                    |-> output_signal == $past(output_signal) );

  // No X/Z on output when out of reset
  assert property ( reset |-> !$isunknown(output_signal) );

  // Output only changes on posedge clk or negedge reset
  assert property ( $changed(output_signal) |-> ($rose(clk) || $fell(reset)) );

  // Coverage
  cover property (@(negedge reset) 1);         // reset asserted
  cover property ( $rose(reset) );             // reset deasserted
  cover property ( @(posedge clk)
                   reset && $past(reset) &&
                   output_signal == $past(input_signal[15:12]) &&
                   output_signal != $past(output_signal) ); // an update

  genvar i;
  for (i = 0; i < 16; i++) begin : cov_out_vals
    cover property ( @(posedge clk) reset && output_signal == i[3:0] );
  end
endmodule

// Bind into DUT
bind output_signal_module output_signal_module_sva sva_i(
  .clk(clk), .reset(reset), .input_signal(input_signal), .output_signal(output_signal)
);