// SVA for sky130_fd_sc_hdll__isobufsrc
// Function: X = A & ~SLEEP

module sky130_fd_sc_hdll__isobufsrc_sva
(
  input logic X,
  input logic SLEEP,
  input logic A
);

  default clocking cb @ (posedge $global_clock); endclocking

  // Functional equivalence (4-state)
  assert property (X === (A & ~SLEEP))
    else $error("Functional mismatch: X != (A & ~SLEEP)");

  // X known whenever inputs are known
  assert property (!$isunknown({A,SLEEP}) |-> !$isunknown(X))
    else $error("X is X/Z while inputs are known");

  // Sleep gating and follow behavior (redundant to functional, clearer debug)
  assert property (SLEEP === 1'b1 |-> X === 1'b0)
    else $error("Sleep gating violated: X must be 0 when SLEEP=1");
  assert property (SLEEP === 1'b0 |-> X === A)
    else $error("Awake follow violated: X must equal A when SLEEP=0");

  // Output only changes if an input changed
  assert property ($changed(X) |-> ($changed(A) or $changed(SLEEP)))
    else $error("Spurious X change without input change");

  // Coverage: truth table
  cover property (SLEEP==0 && A==0 && X==0);
  cover property (SLEEP==0 && A==1 && X==1);
  cover property (SLEEP==1 && A==0 && X==0);
  cover property (SLEEP==1 && A==1 && X==0);

  // Coverage: key transitions
  cover property (SLEEP==0 && A==1 ##1 SLEEP==1 && X==0); // go to sleep, force 0
  cover property (SLEEP==1 && A==1 ##1 SLEEP==0 && X==1); // wake, follow A
  cover property (SLEEP==1 && X==0 ##1 $changed(A) && X==0); // A toggles while asleep, X holds 0
  cover property (SLEEP==0 && A==0 ##1 A==1 && X==1); // A toggle while awake, X follows

endmodule

bind sky130_fd_sc_hdll__isobufsrc sky130_fd_sc_hdll__isobufsrc_sva sva_i (.*);