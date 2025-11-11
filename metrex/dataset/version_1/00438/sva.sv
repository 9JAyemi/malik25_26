// SVA checker for OAI22X1
// Self-clocked on any input transition; bind to the DUT instance.
// Focuses on functional equivalence, determinism/X-handling, and key internal consistency.
// Add one bind per DUT instance:
//   bind OAI22X1 OAI22X1_sva sva(.A(A), .B(B), .C(C), .Y(Y),
//                                 .X1(X1), .X2(X2), .X3(X3), .X4(X4), .X5(X5), .X6(X6), .X7(X7), .X8(X8),
//                                 .X9(X9), .X10(X10), .X11(X11), .X12(X12), .X13(X13), .X14(X14), .X15(X15), .X16(X16));

module OAI22X1_sva(
  input logic A, B, C, Y,
  input logic X1, X2, X3, X4, X5, X6, X7, X8,
  input logic X9, X10, X11, X12, X13, X14, X15, X16
);
  // Sample on any input change
  default clocking cb @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C); endclocking

  // Functional spec: Y = C & (~A | ~B); check when inputs are known
  assert property (!$isunknown({A,B,C}) |-> (Y == (C & (~A | ~B))));

  // Deterministic/X-robust cases
  assert property ((C == 1'b0) |-> (Y == 1'b0 && !$isunknown(Y)));
  assert property ((C && !A)    |-> (Y == 1'b1 && !$isunknown(Y)));
  assert property ((C && !B)    |-> (Y == 1'b1 && !$isunknown(Y)));
  assert property ((C && A && B)|-> (Y == 1'b0 && !$isunknown(Y)));

  // Output known if inputs known
  assert property (!$isunknown({A,B,C}) |-> !$isunknown(Y));

  // Internal canonical minterms (concise but strong)
  assert property (X3  === (C & ~A & ~B));
  assert property (X13 === (C & ~A &  B));
  assert property (X16 === (C &  A & ~B));
  assert property (X8  === X3);  // duplicate path must match

  // Final composition equivalence
  assert property (Y === (X3 | X8 | X13 | X16));

  // Lightweight redundancy/alias checks (4-state equality)
  assert property (X2 === C && X7 === C && X12 === C);
  assert property (X4 === ~A && X9 === ~A);
  assert property (X5 === ~B && X15 === ~B);

  // Coverage: all input combinations
  cover property (A==0 && B==0 && C==0);
  cover property (A==0 && B==0 && C==1);
  cover property (A==0 && B==1 && C==0);
  cover property (A==0 && B==1 && C==1);
  cover property (A==1 && B==0 && C==0);
  cover property (A==1 && B==0 && C==1);
  cover property (A==1 && B==1 && C==0);
  cover property (A==1 && B==1 && C==1);

  // Coverage: each one-hot product term exercised
  cover property (X3);
  cover property (X13);
  cover property (X16);

  // Coverage: output toggles
  cover property (!Y ##1 Y);
  cover property ( Y ##1 !Y);
endmodule