// SVA for data_out_on_rising_edge
module data_out_on_rising_edge_sva (input logic clk, data_in, data_out);
  default clocking cb @(posedge clk); endclocking

  // Guard $past on first cycle
  logic past_valid;
  initial past_valid = 0;
  always @(posedge clk) past_valid <= 1;
  default disable iff (!past_valid)

  // 1-cycle flop behavior: output equals prior-cycle input
  a_ff_behavior: assert property (data_out == $past(data_in));

  // If input holds across cycles, output holds across cycles
  a_hold_when_in_stable: assert property ((data_in == $past(data_in)) |-> (data_out == $past(data_out)));

  // When prior input is known, output must be known and match it
  a_known_out_when_prev_in_known: assert property ((!$isunknown($past(data_in))) |-> (! $isunknown(data_out) && data_out == $past(data_in)));

  // Coverage: both values transfer and toggle propagates
  c_pass_zero:  cover property (data_in == 1'b0 ##1 data_out == 1'b0);
  c_pass_one:   cover property (data_in == 1'b1 ##1 data_out == 1'b1);
  c_toggle:     cover property ($changed(data_in) ##1 $changed(data_out));
endmodule

bind data_out_on_rising_edge data_out_on_rising_edge_sva sva_i (.clk(clk), .data_in(data_in), .data_out(data_out));