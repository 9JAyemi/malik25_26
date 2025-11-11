// SVA checker for sky130_fd_sc_ms__a22o
// Focus: functional equivalence, quadrant-specific behavior, and full truth-table coverage.

module a22o_sva (
  input logic A1, A2, B1, B2, X
);
  // Reference function
  logic ref;
  assign ref = ((A1 & ~A2) | (B1 & ~B2) | (~A1 & ~A2 & ~B1 & ~B2));

  // Core functional equivalence (inputs known)
  assert property (disable iff ($isunknown({A1,A2,B1,B2})) X == ref);

  // Quadrant-specific assertions (inputs known)
  assert property (disable iff ($isunknown({A1,A2,B1,B2})) ( A2 &&  B2) |-> !X);
  assert property (disable iff ($isunknown({A1,A2,B1,B2})) ( A2 && !B2) |-> (X == B1));
  assert property (disable iff ($isunknown({A1,A2,B1,B2})) (!A2 &&  B2) |-> (X == A1));
  assert property (disable iff ($isunknown({A1,A2,B1,B2})) (!A2 && !B2) |->  X);

  // Full truth-table coverage (16 minterms, with expected X)
  // A2=1, B2=1 -> X=0 always
  cover property (!A1 &&  A2 && !B1 &&  B2 && !X);
  cover property (!A1 &&  A2 &&  B1 &&  B2 && !X);
  cover property ( A1 &&  A2 && !B1 &&  B2 && !X);
  cover property ( A1 &&  A2 &&  B1 &&  B2 && !X);

  // A2=1, B2=0 -> X=B1
  cover property (!A1 &&  A2 && !B1 && !B2 && !X);
  cover property (!A1 &&  A2 &&  B1 && !B2 &&  X);
  cover property ( A1 &&  A2 && !B1 && !B2 && !X);
  cover property ( A1 &&  A2 &&  B1 && !B2 &&  X);

  // A2=0, B2=1 -> X=A1
  cover property (!A1 && !A2 && !B1 &&  B2 && !X);
  cover property (!A1 && !A2 &&  B1 &&  B2 && !X);
  cover property ( A1 && !A2 && !B1 &&  B2 &&  X);
  cover property ( A1 && !A2 &&  B1 &&  B2 &&  X);

  // A2=0, B2=0 -> X=1 always
  cover property (!A1 && !A2 && !B1 && !B2 &&  X);
  cover property (!A1 && !A2 &&  B1 && !B2 &&  X);
  cover property ( A1 && !A2 && !B1 && !B2 &&  X);
  cover property ( A1 && !A2 &&  B1 && !B2 &&  X);
endmodule

// Bind to DUT
bind sky130_fd_sc_ms__a22o a22o_sva u_a22o_sva (.A1(A1), .A2(A2), .B1(B1), .B2(B2), .X(X));