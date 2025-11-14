// SVA for clock_gate_flop
// Concise, full functional checks with coverage.
// Bind this to the DUT.

module clock_gate_flop_sva (input logic clk, en, gated_clk);
  default clocking cb @(posedge clk); endclocking

  // Functional mapping (4-state exact): gated_clk = (en was 1) at previous posedge
  a_func_map: assert property (cb $past_valid |-> gated_clk == ($past(en) === 1'b1));

  // Sanity: inputs/outputs known after first sampled cycle
  a_en_known:  assert property (cb $past_valid |-> !$isunknown(en));
  a_out_known: assert property (cb $past_valid |-> !$isunknown(gated_clk));

  // Directional consistency on output edges
  a_rise_reason: assert property (cb $rose(gated_clk) |-> $past(en) === 1'b1);
  a_fall_reason: assert property (cb $fell(gated_clk) |-> $past(en) !== 1'b1);

  // Coverage: exercise both enable directions and corresponding outputs
  c_en_rise:  cover property (cb $rose(en));
  c_en_fall:  cover property (cb $fell(en));
  c_out_rise: cover property (cb $rose(gated_clk));
  c_out_fall: cover property (cb $fell(gated_clk));
  c_en1_out1: cover property (cb en ##1 gated_clk);
  c_en0_out0: cover property (cb !en ##1 !gated_clk);
endmodule

bind clock_gate_flop clock_gate_flop_sva u_clock_gate_flop_sva(.clk(clk), .en(en), .gated_clk(gated_clk));