// SVA for add_sub
// Notes:
// - C is both clock and mode; because the always blocks are posedge C and test C==1 inside,
//   the subtraction path is unreachable. Assertions below both verify actual behavior and
//   flag that subtraction never occurs.

module add_sub_sva (
  input  logic       C,
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic [3:0] Q,
  input  logic [3:0] sum_reg,
  input  logic [3:0] sub_reg
);
  default clocking cb @(posedge C); endclocking

  // Handle first-cycle $past
  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge C) past_valid <= 1'b1;

  // Inputs should be known at sampling
  a_known_inputs: assert property (past_valid |-> !$isunknown({A,B}));

  // On each posedge, after NBA updates, sum_reg must equal A+B (4-bit wrap)
  a_sum_update:   assert property (1'b1 |-> ##0 (sum_reg == (A + B)));

  // Q reflects previous cycle's A+B due to two-stage register chain
  a_q_prev_sum:   assert property (past_valid |-> ##0 (Q == $past(A + B)));

  // No updates on negedge (sequential logic only at posedge)
  a_no_negedge_updates: assert property (@(negedge C)
                                        $stable(sum_reg) && $stable(sub_reg) && $stable(Q));

  // Subtraction path is effectively unreachable: sub_reg never changes across posedges
  a_sub_never_updates:  assert property (past_valid |-> sub_reg == $past(sub_reg));

  // Basic functional coverage
  // Q changes at a posedge (some activity)
  c_q_changes:     cover property (past_valid ##0 (Q != $past(Q)));

  // Overflow wrap case: 0xF + 1 -> 0x0 in sum_reg; Q matches previous sum
  c_add_overflow:  cover property (past_valid && ($past(A)==4'hF) && ($past(B)==4'h1)
                                   ##0 (sum_reg==4'h0) && (Q == $past(A+B)));

  // Zero + zero
  c_add_zero:      cover property (past_valid && ($past(A)==4'h0) && ($past(B)==4'h0)
                                   ##0 (sum_reg==4'h0) && (Q == $past(A+B)));

  // Attempt to see subtraction activity (should remain uncovered)
  c_sub_change:    cover property (sub_reg != $past(sub_reg));

endmodule

// Bind into the DUT (tool: place in testbench or a separate bind file)
bind add_sub add_sub_sva sva_i (
  .C(C),
  .A(A),
  .B(B),
  .Q(Q),
  .sum_reg(sum_reg),
  .sub_reg(sub_reg)
);