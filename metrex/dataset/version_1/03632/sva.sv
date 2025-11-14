// SVA checker for custom_module
module custom_module_sva (
  input logic A1, A2, A3, A4, B1, X,
  input logic X1, X2
);

  // Sample on any relevant signal change
  default clocking cb @(A1 or A2 or A3 or A4 or B1 or X1 or X2 or X); endclocking

  // Functional correctness of internal nodes and output
  assert property (!$isunknown({A1,A2})           |-> (X1 === (A1 & A2)));
  assert property (!$isunknown({A3,A4})           |-> (X2 === (A3 & A4)));
  assert property (!$isunknown({X1,X2,B1})        |-> (X  === ~(X1 | X2 | B1)));
  assert property (!$isunknown({A1,A2,A3,A4,B1})  |-> (X  === ~((A1 & A2) | (A3 & A4) | B1)));

  // Deterministic effects and consistency
  assert property ((B1 == 1'b1) |-> (X == 1'b0));
  assert property ((X1 == 1'b1) |-> (X == 1'b0));
  assert property ((X2 == 1'b1) |-> (X == 1'b0));
  assert property ((X  == 1'b1) |-> (B1 == 1'b0 && X1 == 1'b0 && X2 == 1'b0));

  // Knownness when inputs known
  assert property (!$isunknown({A1,A2})           |-> !$isunknown(X1));
  assert property (!$isunknown({A3,A4})           |-> !$isunknown(X2));
  assert property (!$isunknown({A1,A2,A3,A4,B1})  |-> !$isunknown(X));

  // Coverage: key functional scenarios and toggles
  cover property (B1==1'b0 && !(A1&A2) && !(A3&A4) && X==1'b1); // X=1 case
  cover property (B1==1'b1 && !(A1&A2) && !(A3&A4) && X==1'b0); // only B1 active
  cover property (B1==1'b0 &&  (A1&A2) && !(A3&A4) && X==1'b0); // only X1 active
  cover property (B1==1'b0 && !(A1&A2) &&  (A3&A4) && X==1'b0); // only X2 active
  cover property (B1==1'b0 &&  (A1&A2) &&  (A3&A4) && X==1'b0); // X1 and X2 active
  cover property (B1==1'b1 &&  (A1&A2) &&  (A3&A4) && X==1'b0); // all three active

  cover property (@(posedge X));
  cover property (@(negedge X));
  cover property (@(posedge X1));
  cover property (@(negedge X1));
  cover property (@(posedge X2));
  cover property (@(negedge X2));

endmodule

// Bind into DUT; X1/X2 are internal wires resolved in the bound scope
bind custom_module custom_module_sva sva_i (
  .A1(A1), .A2(A2), .A3(A3), .A4(A4), .B1(B1), .X(X), .X1(X1), .X2(X2)
);