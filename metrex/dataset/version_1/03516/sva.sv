// SVA for sky130_fd_sc_ms__o211a_4
// Bind this module to the DUT to check combinational correctness and basic coverage.

module sky130_fd_sc_ms__o211a_4_sva (
  input X,
  input A1,
  input A2,
  input B1,
  input C1,
  input VPWR,
  input VGND,
  input VPB,
  input VNB
);

  // Convenience expressions
  wire rails_ok = VPWR & ~VGND & VPB & ~VNB;
  wire full_fn  = A1 & A2 & B1 & C1 & rails_ok;

  // Functional equivalence (full truth table as coded)
  assert property (X == (A1 & A2 & B1 & C1 & VPWR & !VGND & VPB & !VNB));

  // Under valid rails, output equals A1&A2&B1&C1
  assert property (rails_ok |-> (X == (A1 & A2 & B1 & C1)));

  // Dominance: any low input (or invalid rail) forces X low
  assert property (!A1 |-> !X);
  assert property (!A2 |-> !X);
  assert property (!B1 |-> !X);
  assert property (!C1 |-> !X);
  assert property (!VPWR |-> !X);
  assert property ( VGND |-> !X);
  assert property (!VPB  |-> !X);
  assert property ( VNB  |-> !X);

  // No X/Z on X when rails are valid and inputs are known
  assert property (rails_ok && !$isunknown({A1,A2,B1,C1}) |-> !$isunknown(X));

  // Basic coverage
  cover property (rails_ok &&  X);                      // reachable high
  cover property (rails_ok && !X);                      // reachable low
  cover property (full_fn && X);                        // all inputs+rails high -> X high
  cover property (rails_ok && !A1 &&  A2 &&  B1 &&  C1 && !X);
  cover property (rails_ok &&  A1 && !A2 &&  B1 &&  C1 && !X);
  cover property (rails_ok &&  A1 &&  A2 && !B1 &&  C1 && !X);
  cover property (rails_ok &&  A1 &&  A2 &&  B1 && !C1 && !X);
  cover property ((!VPWR || VGND || !VPB || VNB) && !X);

endmodule

// Bind to the DUT
bind sky130_fd_sc_ms__o211a_4 sky130_fd_sc_ms__o211a_4_sva sva (
  .X(X), .A1(A1), .A2(A2), .B1(B1), .C1(C1),
  .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB)
);