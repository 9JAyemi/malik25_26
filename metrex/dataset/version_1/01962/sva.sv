// SVA for the provided design. Bind these to the DUT.
// Focused, high-signal-utility checks with minimal but meaningful coverage.

////////////////////////////////////////////////////////////
// shift_reg assertions (intended 1-bit serial-in behavior)
// This will flag the width/concatenation bug in the RTL.
module shift_reg_sva (input clk, input [7:0] d, input [7:0] q);
  default clocking cb @(posedge clk); endclocking
  bit past_valid; always @(posedge clk) past_valid <= 1'b1;

  // No X/Z after first cycle
  assert property (past_valid |-> !$isunknown({d, q}));

  // Intended shift: shift left by 1, shift-in d[0]
  assert property (past_valid |-> q == { $past(q[6:0]), $past(d[0]) });

  // Coverage: exercise both shift-in 0 and 1 and any shift activity
  cover property (past_valid && $changed(q));
  cover property (past_valid && $rose(d[0]));
  cover property (past_valid && $fell(d[0]));
endmodule

bind shift_reg shift_reg_sva u_shift_reg_sva(.clk(clk), .d(d), .q(q));


////////////////////////////////////////////////////////////
// d_ff assertions (negedge-sampled DFF)
module d_ff_sva (input clk, input d, input q);
  default clocking cb @(negedge clk); endclocking
  bit past_valid; always @(negedge clk) past_valid <= 1'b1;

  // No X/Z after first negedge
  assert property (past_valid |-> !$isunknown({d, q}));

  // Functional: 1-cycle latency at negedge domain
  assert property (past_valid |-> q == $past(d));

  // Coverage: observe toggling
  cover property (past_valid && $changed(q));
endmodule

bind d_ff d_ff_sva u_dff_sva(.clk(clk), .d(d), .q(q));


////////////////////////////////////////////////////////////
// Top-level structural/temporal connectivity checks
module top_sva (
  input clk,
  input [7:0] d,
  input [7:0] shift_reg_out,
  input [0:0] d_ff_out,
  input [15:0] q
);
  default clocking cb @(posedge clk); endclocking
  bit past_valid; always @(posedge clk) past_valid <= 1'b1;

  // Concat mapping: q = {shift_reg_out, d_ff_out} zero-extended to 16 bits
  assert property (past_valid |-> (q[7:0] == shift_reg_out &&
                                   q[8]   == d_ff_out[0]   &&
                                   q[15:9]== '0));

  // Cross-edge connectivity: d_ff samples shift_reg_out[7] at negedge
  // (at each negedge, d_ff_out equals prior negedge value of shift_reg_out[7])
  assert property (@(negedge clk) d_ff_out[0] == $past(shift_reg_out[7]));

  // Sanity: no X/Z on concatenated output bits after first posedge
  assert property (past_valid |-> !$isunknown({shift_reg_out, d_ff_out, q}));

  // Coverage: observe both 0 and 1 on d_ff_out reflected into q[8]
  cover property (past_valid && d_ff_out[0] && q[8]);
  cover property (past_valid && !d_ff_out[0] && !q[8]);
endmodule

bind top_module top_sva u_top_sva(
  .clk(clk),
  .d(d),
  .shift_reg_out(shift_reg_out),
  .d_ff_out(d_ff_out),
  .q(q)
);