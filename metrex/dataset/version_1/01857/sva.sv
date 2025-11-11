// SVA checker for sky130_fd_sc_lp__a32o
module sky130_fd_sc_lp__a32o_sva (
  input logic A1, A2, A3, B1, B2, VPWR, VGND, VPB, VNB,
  input logic X
);
  // Functional reference
  wire base = (A1 & ~A2 & ~A3 & ~B1 & ~B2 & ~VPWR & ~VGND & ~VPB & ~VNB);

  // Exact functional equivalence (4-state accurate)
  ap_eq:           assert property (X === base);

  // Output must be known if all inputs are known
  ap_known:        assert property (!$isunknown({A1,A2,A3,B1,B2,VPWR,VGND,VPB,VNB}) |-> !$isunknown(X));

  // Any inhibitor high or A1 low forces output low (strong invariant)
  ap_inhibit_low:  assert property ( (!A1) || A2 || A3 || B1 || B2 || VPWR || VGND || VPB || VNB |-> (X==1'b0) );

  // Sanity under nominal power (if used): VPWR=1, VGND=0 implies X=0
  ap_power_sane:   assert property ( VPWR && !VGND |-> X==1'b0 );

  // Coverage
  // Hit the sole minterm where X must be 1
  cp_x1:           cover property ( base && X );

  // Each single-bit violation of the minterm must drive X low (and be observed)
  cp_block_A1:     cover property ( !A1 && !A2 && !A3 && !B1 && !B2 && !VPWR && !VGND && !VPB && !VNB && (X==1'b0) );
  cp_block_A2:     cover property (  A1 &&  A2 && !A3 && !B1 && !B2 && !VPWR && !VGND && !VPB && !VNB && (X==1'b0) );
  cp_block_A3:     cover property (  A1 && !A2 &&  A3 && !B1 && !B2 && !VPWR && !VGND && !VPB && !VNB && (X==1'b0) );
  cp_block_B1:     cover property (  A1 && !A2 && !A3 &&  B1 && !B2 && !VPWR && !VGND && !VPB && !VNB && (X==1'b0) );
  cp_block_B2:     cover property (  A1 && !A2 && !A3 && !B1 &&  B2 && !VPWR && !VGND && !VPB && !VNB && (X==1'b0) );
  cp_block_VPWR:   cover property (  A1 && !A2 && !A3 && !B1 && !B2 &&  VPWR && !VGND && !VPB && !VNB && (X==1'b0) );
  cp_block_VGND:   cover property (  A1 && !A2 && !A3 && !B1 && !B2 && !VPWR &&  VGND && !VPB && !VNB && (X==1'b0) );
  cp_block_VPB:    cover property (  A1 && !A2 && !A3 && !B1 && !B2 && !VPWR && !VGND &&  VPB && !VNB && (X==1'b0) );
  cp_block_VNB:    cover property (  A1 && !A2 && !A3 && !B1 && !B2 && !VPWR && !VGND && !VPB &&  VNB && (X==1'b0) );

  // Output activity
  cp_rise:         cover property ($rose(X));
  cp_fall:         cover property ($fell(X));
endmodule

// Bind into the DUT
bind sky130_fd_sc_lp__a32o sky130_fd_sc_lp__a32o_sva sva_i (.*);