// SVA checker for module_name
module module_name_sva (
  input logic A1, A2, A3, B1,
  input logic Y,
  input logic VPWR, VGND, VPB, VNB
);

  // Functional correctness (4-state exact equivalence)
  assert property ( Y === ((A1 & A2 & A3 & ~B1) | (~A1 & ~A2 & ~A3 & B1)) )
    else $error("Y does not match boolean spec");

  // Y must be known when inputs are known
  assert property ( !$isunknown({A1,A2,A3,B1}) |-> !$isunknown(Y) )
    else $error("Y unknown with known inputs");

  // Terms that drive Y high are mutually exclusive
  assert property ( !((A1 & A2 & A3 & ~B1) && (~A1 & ~A2 & ~A3 & B1)) )
    else $error("Mutually exclusive minterms both true");

  // Output changes only when inputs change (combinational sanity)
  assert property ( $changed(Y) |-> $changed({A1,A2,A3,B1}) )
    else $error("Y changed without input change");

  // Power/ground rails tied correctly
  assert property ( (VPWR === 1'b1) && (VPB === 1'b1) && (VGND === 1'b0) && (VNB === 1'b0) )
    else $error("Power/ground rails not at expected constants");

  // Coverage
  cover property ( (A1 & A2 & A3 & ~B1) && (Y === 1'b1) );
  cover property ( (~A1 & ~A2 & ~A3 & B1) && (Y === 1'b1) );
  cover property ( !$isunknown({A1,A2,A3,B1}) && (Y === 1'b0) );
  cover property ( $rose(Y) );
  cover property ( $fell(Y) );

endmodule

// Bind into the DUT
bind module_name module_name_sva sva (
  .A1(A1), .A2(A2), .A3(A3), .B1(B1), .Y(Y),
  .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB)
)