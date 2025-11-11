// SVA for my_module (concise, full functional and independence checks, plus coverage)

module my_module_sva (
  input logic Y,
  input logic A1, A2,
  input logic B1, B2,
  input logic VPWR, VGND, VPB, VNB
);
  default clocking cb @(*) ; endclocking

  // Power assumptions (formal-friendly)
  assume property ( !$isunknown({VPWR,VGND,VPB,VNB}) );
  assume property ( VPWR === 1'b1 && VGND === 1'b0 );
  assume property ( VPB  === VPWR && VNB  === VGND );

  // Functional correctness and determinism
  assert property ( Y === (A1 & A2) );
  assert property ( $stable({A1,A2}) |-> $stable(Y) );

  // X-prop: when inputs known, output known
  assert property ( !$isunknown({A1,A2}) |-> !$isunknown(Y) );

  // Independence from unused inputs
  assert property ( $changed(B1) && $stable({A1,A2}) |-> $stable(Y) );
  assert property ( $changed(B2) && $stable({A1,A2}) |-> $stable(Y) );

  // Basic functional coverage
  cover property ( A1==0 && A2==0 && Y==0 );
  cover property ( A1==0 && A2==1 && Y==0 );
  cover property ( A1==1 && A2==0 && Y==0 );
  cover property ( A1==1 && A2==1 && Y==1 );
  cover property ( $rose(Y) );
  cover property ( $fell(Y) );
endmodule

bind my_module my_module_sva my_module_sva_i (.*);