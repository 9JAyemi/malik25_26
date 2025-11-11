// SVA for sky130_fd_sc_hdll__inputiso0n
// Function: X = A & SLEEP_B  (isolation active when SLEEP_B=0)

module sky130_fd_sc_hdll__inputiso0n_sva (
  input logic X,
  input logic A,
  input logic SLEEP_B
);

  // Sample on any relevant edge
  default clocking cb @(
    posedge A or negedge A or
    posedge SLEEP_B or negedge SLEEP_B or
    posedge X or negedge X
  ); endclocking

  // Functional correctness
  assert property (X === (A & SLEEP_B))
    else $error("FUNC: X != (A & SLEEP_B)");

  // Isolation mode (SLEEP_B=0)
  assert property (!SLEEP_B |-> (X == 1'b0))
    else $error("ISO: SLEEP_B=0 but X!=0");
  assert property (!SLEEP_B && $changed(A) |-> !$changed(X))
    else $error("ISO: X changed while isolated (SLEEP_B=0)");

  // Pass-through mode (SLEEP_B=1)
  assert property (SLEEP_B |-> (X === A))
    else $error("PASS: SLEEP_B=1 but X!=A");
  assert property (SLEEP_B && $rose(A) |-> $rose(X))
    else $error("PASS: A rise not mirrored on X");
  assert property (SLEEP_B && $fell(A) |-> $fell(X))
    else $error("PASS: A fall not mirrored on X");

  // Sleep edge behavior
  assert property ($rose(SLEEP_B) |-> (X === A))
    else $error("EDGE: On SLEEP_B rise, X!=A");
  assert property ($fell(SLEEP_B) |-> (X == 1'b0))
    else $error("EDGE: On SLEEP_B fall, X!=0");

  // No X/Z on output when inputs known
  assert property (!$isunknown({A,SLEEP_B}) |-> !$isunknown(X))
    else $error("XZ: X is X/Z while inputs known");

  // Coverage: truth table states
  cover property (!A && !SLEEP_B && !X);
  cover property (!A &&  SLEEP_B && !X);
  cover property ( A && !SLEEP_B && !X);
  cover property ( A &&  SLEEP_B &&  X);

  // Coverage: mode/edge activity
  cover property ($rose(SLEEP_B));
  cover property ($fell(SLEEP_B));
  cover property ( SLEEP_B && ($rose(A) || $fell(A)));
  cover property (!SLEEP_B && ($rose(A) || $fell(A)));

endmodule

bind sky130_fd_sc_hdll__inputiso0n sky130_fd_sc_hdll__inputiso0n_sva sva (.*);