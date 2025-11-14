// SVA for sky130_fd_sc_hd__lpflow_inputiso1p
// Function: X == (A | SLEEP). When SLEEP=1, X is clamped to 1; when SLEEP=0, X=A.

module sky130_fd_sc_hd__lpflow_inputiso1p_sva (
  input logic A,
  input logic SLEEP,
  input logic X
);

  // Core functional equivalence (4-state aware)
  assert property (@(A or SLEEP or X) X === (A | SLEEP))
    else $error("X != (A | SLEEP)");

  // Mode-specific implications
  assert property (@(A or SLEEP or X) SLEEP |-> (X === 1'b1));
  assert property (@(A or SLEEP or X) !SLEEP |-> (X === A));

  // Edge-based reactions
  assert property (@(posedge SLEEP) X === 1'b1);
  assert property (@(negedge SLEEP) X === A);

  // No X/Z on X when inputs are known
  assert property (@(A or SLEEP or X) (!$isunknown(A) && !$isunknown(SLEEP)) |-> !$isunknown(X));

  // Coverage: truth table points
  cover property (@(A or SLEEP or X) (!A && !SLEEP && X === 1'b0));
  cover property (@(A or SLEEP or X) (!A &&  SLEEP && X === 1'b1));
  cover property (@(A or SLEEP or X) ( A && !SLEEP && X === 1'b1));
  cover property (@(A or SLEEP or X) ( A &&  SLEEP && X === 1'b1));

  // Coverage: dynamic behavior
  cover property (@(A or SLEEP or X) (!SLEEP && $changed(A) && $changed(X)));   // pass-through toggling
  cover property (@(A or SLEEP or X) ( SLEEP && $changed(A) && !$changed(X)));  // clamped while A toggles
  cover property (@(posedge SLEEP) X === 1'b1);
  cover property (@(negedge SLEEP) X === A);
  cover property (@(posedge X));
  cover property (@(negedge X));

endmodule

bind sky130_fd_sc_hd__lpflow_inputiso1p sky130_fd_sc_hd__lpflow_inputiso1p_sva XCHK (.A(A), .SLEEP(SLEEP), .X(X));