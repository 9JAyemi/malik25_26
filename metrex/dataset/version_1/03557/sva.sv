// SVA checker for a221o_2
module a221o_2_sva (
  input logic X,
  input logic A1, A2, B1, B2, C1,
  input logic Y
);
  default clocking cb @(*) endclocking

  // Functional equivalence under known relevant inputs
  assert property (!$isunknown({A1,A2,B1,B2,C1}) |-> (Y === ((A1 & B1 & C1) | (A2 & B2 & C1))));

  // Mandatory gating: C1=0 forces Y=0 (holds even with unknowns on others)
  assert property ((C1 === 1'b0) |-> (Y === 1'b0));

  // Each product term drives Y when C1=1
  assert property ((C1 === 1'b1 && A1 === 1'b1 && B1 === 1'b1) |-> (Y === 1'b1));
  assert property ((C1 === 1'b1 && A2 === 1'b1 && B2 === 1'b1) |-> (Y === 1'b1));

  // With C1=1 and both products false, Y=0
  assert property ((C1 === 1'b1 && (A1 === 1'b0 || B1 === 1'b0) && (A2 === 1'b0 || B2 === 1'b0)) |-> (Y === 1'b0));

  // If relevant inputs are known, Y must be known
  assert property (!$isunknown({A1,A2,B1,B2,C1}) |-> !$isunknown(Y));

  // Independence from unused input X: changing X alone cannot change Y
  assert property (@(posedge X or negedge X) $stable({A1,A2,B1,B2,C1}) |-> $stable(Y));

  // Functional coverage (key scenarios)
  cover property (C1==1 && A1==1 && B1==1 && A2==0 && B2==0 && Y==1); // only A1&B1 path
  cover property (C1==1 && A2==1 && B2==1 && A1==0 && B1==0 && Y==1); // only A2&B2 path
  cover property (C1==1 && A1==1 && B1==1 && A2==1 && B2==1 && Y==1); // both paths
  cover property (C1==1 && ((A1==0 || B1==0) && (A2==0 || B2==0)) && Y==0); // none with C1=1
  cover property (C1==0 && Y==0); // C1 gating low
  cover property ($rose(Y));
  cover property ($fell(Y));
  cover property (@(posedge X or negedge X) $stable({A1,A2,B1,B2,C1}) ##0 $stable(Y)); // X-independence seen
endmodule

// Bind into DUT
bind a221o_2 a221o_2_sva sva_i (.*);