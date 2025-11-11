// SVA for sky130_fd_sc_hd__o41a: X = (A1 | A2 | A3 | A4) & B1
// Bind into the DUT to check ports and internal nets.
module sky130_fd_sc_hd__o41a_sva;
  // Bound inside sky130_fd_sc_hd__o41a instance; can see ports and internal nets.
  default clocking cb @(*); endclocking

  // Functional equivalence (4-state and 2-state under known inputs)
  assert property (X === ((A1 || A2 || A3 || A4) && B1));
  assert property (!$isunknown({A1,A2,A3,A4,B1}) |-> X == ((A1 || A2 || A3 || A4) && B1));

  // Controlling-value invariants
  assert property (B1 === 1'b0 |-> X === 1'b0);
  assert property ((A1===1'b0 && A2===1'b0 && A3===1'b0 && A4===1'b0) |-> X === 1'b0);
  assert property (B1 === 1'b1 && (A1 || A2 || A3 || A4) |-> X === 1'b1);

  // Internal net consistency with primitives
  assert property (or0_out     === (A1 || A2 || A3 || A4));
  assert property (and0_out_X  === (or0_out && B1));
  assert property (X === and0_out_X);

  // Edge-causality checks
  assert property (@(posedge X) B1 && (A1 || A2 || A3 || A4));
  assert property (@(negedge X) (!B1) || (!A1 && !A2 && !A3 && !A4));

  // X must be known when forced by controlling values
  assert property ( (B1===1'b0) ||
                    (A1===1'b0 && A2===1'b0 && A3===1'b0 && A4===1'b0) ||
                    (B1===1'b1 && (A1 || A2 || A3 || A4)) |-> !$isunknown(X));

  // Coverage: basic modes and single-driver scenarios
  cover property (B1==1'b0 && X==1'b0);
  cover property (B1==1'b1 && !(A1||A2||A3||A4) && X==1'b0);
  cover property (B1==1'b1 &&  (A1||A2||A3||A4) && X==1'b1);
  cover property (B1 &&  A1 && !A2 && !A3 && !A4 && X);
  cover property (B1 && !A1 &&  A2 && !A3 && !A4 && X);
  cover property (B1 && !A1 && !A2 &&  A3 && !A4 && X);
  cover property (B1 && !A1 && !A2 && !A3 &&  A4 && X);
  cover property (@(posedge X) 1'b1);
  cover property (@(negedge X) 1'b1);
endmodule

bind sky130_fd_sc_hd__o41a sky130_fd_sc_hd__o41a_sva sva_o41a();