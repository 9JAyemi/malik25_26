// SVA for my_module
// Binds into DUT and checks combinational correctness, internal equivalence, and basic coverage.

module my_module_sva (
  input logic A1, A2, B1, C1, D1,
  input logic Y,
  input logic and0_out,
  input logic nor0_out_Y
);

  default clocking cb @(posedge $global_clock); endclocking

  // Functional equivalence at known inputs
  property p_func;
    ! $isunknown({A1,A2,B1,C1,D1}) |-> (Y === ~(B1 | C1 | D1 | (A1 & A2)));
  endproperty
  assert property (p_func);

  // Primitive-local equivalences (guard unknowns)
  assert property ( ! $isunknown({A1,A2}) |-> (and0_out    === (A1 & A2)) );
  assert property ( ! $isunknown({B1,C1,D1,and0_out}) |-> (nor0_out_Y === ~(B1 | C1 | D1 | and0_out)) );
  assert property ( ! $isunknown(nor0_out_Y) |-> (Y === nor0_out_Y) );

  // Basic coverage
  cover property ( ! $isunknown({A1,A2,B1,C1,D1}) && (Y==1) );
  cover property ( ! $isunknown({A1,A2,B1,C1,D1}) && (Y==0) );
  cover property ( ! $isunknown({A1,A2}) && and0_out );
  cover property ( ! $isunknown({A1,A2,B1,C1,D1}) ##1 $changed(Y) );

  // Each input can influence Y under suitable conditions
  cover property ( (! $isunknown({A1,A2,B1,C1,D1}) && A2 && !B1 && !C1 && !D1)
                   ##1 (! $isunknown({A1,A2,B1,C1,D1}) && $changed(A1) && $changed(Y)) );
  cover property ( (! $isunknown({A1,A2,B1,C1,D1}) && A1 && !B1 && !C1 && !D1)
                   ##1 (! $isunknown({A1,A2,B1,C1,D1}) && $changed(A2) && $changed(Y)) );
  cover property ( (! $isunknown({A1,A2,B1,C1,D1}) && !(A1&A2) && !C1 && !D1)
                   ##1 (! $isunknown({A1,A2,B1,C1,D1}) && $changed(B1) && $changed(Y)) );
  cover property ( (! $isunknown({A1,A2,B1,C1,D1}) && !(A1&A2) && !B1 && !D1)
                   ##1 (! $isunknown({A1,A2,B1,C1,D1}) && $changed(C1) && $changed(Y)) );
  cover property ( (! $isunknown({A1,A2,B1,C1,D1}) && !(A1&A2) && !B1 && !C1)
                   ##1 (! $isunknown({A1,A2,B1,C1,D1}) && $changed(D1) && $changed(Y)) );

endmodule

bind my_module my_module_sva i_my_module_sva (
  .A1(A1), .A2(A2), .B1(B1), .C1(C1), .D1(D1),
  .Y(Y),
  .and0_out(and0_out),
  .nor0_out_Y(nor0_out_Y)
);