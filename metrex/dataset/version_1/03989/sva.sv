// SVA checker for my_module
module my_module_sva (
  input logic A1,
  input logic A2,
  input logic B1,
  input logic C1,
  input logic X,
  input logic X_int
);

  // Sample on any relevant signal change
  default clocking cb @(A1 or A2 or B1 or C1 or X or X_int); endclocking

  // Functional correctness
  assert property (!$isunknown({B1,C1}) |-> (X === ~(B1 | C1)));
  assert property (!$isunknown({A1,A2}) |-> (X_int === ~(A1 & A2)));

  // Independence: A1/A2 must not affect X (when B1/C1 stable)
  assert property ((($changed(A1) || $changed(A2)) && $stable(B1) && $stable(C1)) |-> $stable(X));

  // Any X change must be caused by B1 or C1
  assert property ($changed(X) |-> ($changed(B1) || $changed(C1)));

  // Basic toggle coverage
  cover property ($rose(X));
  cover property ($fell(X));

  // Functional coverage: NOR truth table
  cover property (B1==0 && C1==0 && X==1);
  cover property (B1==0 && C1==1 && X==0);
  cover property (B1==1 && C1==0 && X==0);
  cover property (B1==1 && C1==1 && X==0);

  // Functional coverage: NAND truth table (internal X_int)
  cover property (A1==0 && A2==0 && X_int==1);
  cover property (A1==0 && A2==1 && X_int==1);
  cover property (A1==1 && A2==0 && X_int==1);
  cover property (A1==1 && A2==1 && X_int==0);

endmodule

// Bind into DUT (accesses internal X_int)
bind my_module my_module_sva u_my_module_sva (
  .A1(A1),
  .A2(A2),
  .B1(B1),
  .C1(C1),
  .X(X),
  .X_int(X_int)
)