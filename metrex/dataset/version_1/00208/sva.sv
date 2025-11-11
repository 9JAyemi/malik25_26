// SVA checker for XOR_GATE
module XOR_GATE_sva (
  input logic A, B, C,
  input logic w1, w2, w3
);
  // Sample on any input edge; ignore checks when inputs are X/Z
  default clocking cb @(posedge A or negedge A or posedge B or negedge B); endclocking
  default disable iff ($isunknown({A,B}));

  // Functional equivalence
  assert property (C == (A ^ B));

  // Internal decomposition checks
  assert property (w1 == (A & ~B));
  assert property (w2 == (~A & B));
  assert property (w3 == (w1 | w2));
  assert property (C  ==  w3);

  // Sanity: no simultaneous set in minterms
  assert property (!(w1 && w2));

  // Knownness when inputs are known
  assert property (!$isunknown({w1,w2,w3,C}));

  // Functional coverage
  cover property (A==0 && B==0 && C==0);
  cover property (A==0 && B==1 && C==1);
  cover property (A==1 && B==0 && C==1);
  cover property (A==1 && B==1 && C==0);
  cover property ($rose(C));
  cover property ($fell(C));
  cover property (w1);
  cover property (w2);
endmodule

// Bind into the DUT to access internal nets
bind XOR_GATE XOR_GATE_sva u_sva(.A(A), .B(B), .C(C), .w1(w1), .w2(w2), .w3(w3));