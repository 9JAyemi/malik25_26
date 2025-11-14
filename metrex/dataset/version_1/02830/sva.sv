// SVA for shift_reg_d_ff
// Focus: correctness, gating, async reset, muxing, and intended shift structure.
// Includes a compile-time width check to catch the shift concatenation bug.

`ifndef SYNTHESIS
module shift_reg_d_ff_sva (
  input        clk,
  input        reset,      // active-low async reset in RTL
  input  [7:0] d,
  input        select,
  input  [7:0] q,
  input  [7:0] shift_reg,
  input  [7:0] d_ff
);

  // Compile-time structural check for the shift expression width
  localparam int SHIFT_EXPR_W = $bits({shift_reg[6:0], d});
  initial assert (SHIFT_EXPR_W == 8)
    else $error("shift_reg_d_ff: width mismatch in shift operation: %0d != 8", SHIFT_EXPR_W);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!reset); // disable while reset is low

  // Output mux correctness (sampled on clock)
  assert property (select |-> q == shift_reg);
  assert property (!select |-> q == d_ff);

  // DFF path: capture and hold
  assert property (!select |=> d_ff == $past(d));          // capture d when selected
  assert property (select  |=> d_ff == $past(d_ff));       // hold when not selected

  // Shift path: hold when not selected, structure when selected
  assert property (!select |=> shift_reg == $past(shift_reg));
  // Intended left-shift structure: new[7:1] == old[6:0]
  assert property (select |=> shift_reg[7:1] == $past(shift_reg[6:0]));

  // Update gating: only the selected path may change
  assert property ((shift_reg != $past(shift_reg)) |-> $past(select));
  assert property ((d_ff      != $past(d_ff))      |-> !$past(select));

  // No X/Z on key signals after reset released
  assert property (!$isunknown({q, shift_reg, d_ff, select}));

  // Asynchronous reset behavior (active-low)
  assert property (@(posedge clk) !reset |-> (shift_reg==8'h34 && d_ff==8'h34 && q==8'h34));
  assert property (@(negedge reset) 1'b1 |-> ##0 (shift_reg==8'h34 && d_ff==8'h34 && q==8'h34));

  // Coverage
  cover property (@(negedge reset) 1);
  cover property (!select ##1 !select && d_ff == $past(d));
  cover property (select  ##1 select  && shift_reg[7:1] == $past(shift_reg[6:0]));
  cover property (!select ##1 select ##1 !select); // mode toggle across both paths

endmodule

bind shift_reg_d_ff shift_reg_d_ff_sva u_shift_reg_d_ff_sva (.*);
`endif