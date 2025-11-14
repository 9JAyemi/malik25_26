// SVA for custom_module
// Bindable, power-aware, concise functional checks + coverage

module custom_module_sva (
  input logic Y,
  input logic A1, A2, A3, B1, B2,
  input logic VPWR, VGND, VPB, VNB
);
  // Power-good qualifier
  wire pg = (VPWR===1'b1) && (VGND===1'b0) && (VPB===1'b1) && (VNB===1'b0);

  default clocking cb @($global_clock); endclocking
  default disable iff (!pg);

  // Functional correctness under known inputs
  assert property ( !$isunknown({A1,A2,A3,B1,B2})
                    |-> Y === (A1 && !A2 && A3 && B1 && !B2) );

  // X-propagation: any unknown on inputs propagates to Y
  assert property ( $isunknown({A1,A2,A3,B1,B2}) |-> $isunknown(Y) );

  // Output changes only when relevant inputs change (no spurious toggles)
  assert property ( $changed(Y) |-> $changed({A1,A2,A3,B1,B2}) );

  // Coverage: observe both output values under power-good with known inputs
  cover property ( !$isunknown({A1,A2,A3,B1,B2}) &&
                   (A1 && !A2 && A3 && B1 && !B2) && Y );
  cover property ( !$isunknown({A1,A2,A3,B1,B2}) &&
                   !(A1 && !A2 && A3 && B1 && !B2) && !Y );

  // Coverage: output transitions
  cover property ( $rose(Y) );
  cover property ( $fell(Y) );

  // Coverage: each input rises and falls at least once
  cover property ( $rose(A1) );  cover property ( $fell(A1) );
  cover property ( $rose(A2) );  cover property ( $fell(A2) );
  cover property ( $rose(A3) );  cover property ( $fell(A3) );
  cover property ( $rose(B1) );  cover property ( $fell(B1) );
  cover property ( $rose(B2) );  cover property ( $fell(B2) );

  // Coverage: X on inputs leads to X on output
  cover property ( $isunknown({A1,A2,A3,B1,B2}) && $isunknown(Y) );
endmodule

// Bind into DUT
bind custom_module custom_module_sva u_custom_module_sva (
  .Y(Y), .A1(A1), .A2(A2), .A3(A3), .B1(B1), .B2(B2),
  .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB)
);