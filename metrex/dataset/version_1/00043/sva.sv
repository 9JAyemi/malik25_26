// SVA for sky130_fd_sc_lp__nor3 (3‑input NOR with output buffer)
// Bind this file to the DUT to check functionality, X/Z semantics, rails, and provide coverage.

`ifndef SKY130_FD_SC_LP__NOR3_SVA
`define SKY130_FD_SC_LP__NOR3_SVA

module sky130_fd_sc_lp__nor3_sva_bind;
  // This module is bound into scope of sky130_fd_sc_lp__nor3.
  // It can directly see A,B,C,Y, VPWR,VGND,VPB,VNB and nor0_out_Y.

  // Combinational sample event for concurrent assertions
  event comb_ev;
  always @(A or B or C or Y or nor0_out_Y or VPWR or VGND or VPB or VNB) -> comb_ev;
  default clocking cb @ (comb_ev); endclocking

  // Power rail checks
  apwr_vpwr: assert property (VPWR === 1'b1);
  apwr_vgnd: assert property (VGND === 1'b0);
  apwr_vpb : assert property (VPB  === 1'b1);
  apwr_vnb : assert property (VNB  === 1'b0);

  // Buffer correctness: Y must equal internal nor output
  abuf_link: assert property (Y === nor0_out_Y);

  // Functional correctness when inputs are all known
  afunc_known: assert property ( !$isunknown({A,B,C}) |-> (Y === ~(A|B|C)) );

  // Dominating-1 semantics: any 1 forces Y=0 even with Xs on others
  adom1: assert property ( (A===1 || B===1 || C===1) |-> (Y === 1'b0) );

  // All zeros forces Y=1
  aall0: assert property ( (A===0 && B===0 && C===0) |-> (Y === 1'b1) );

  // Unmasked Xs propagate to output (no input is 1)
  axprop: assert property (
    ((A===1'bx || B===1'bx || C===1'bx) && !(A===1 || B===1 || C===1)) |-> (Y === 1'bx)
  );

  // No high‑Z on output
  a_no_z: assert property (Y !== 1'bz);

  // No spurious output change without some input change
  a_no_spurious: assert property ( $changed(Y) |-> $changed({A,B,C}) );

  // Coverage: all 8 known input combinations with expected Y
  c000: cover property (A===0 && B===0 && C===0 && Y===1);
  c100: cover property (A===1 && B===0 && C===0 && Y===0);
  c010: cover property (A===0 && B===1 && C===0 && Y===0);
  c001: cover property (A===0 && B===0 && C===1 && Y===0);
  c110: cover property (A===1 && B===1 && C===0 && Y===0);
  c101: cover property (A===1 && B===0 && C===1 && Y===0);
  c011: cover property (A===0 && B===1 && C===1 && Y===0);
  c111: cover property (A===1 && B===1 && C===1 && Y===0);

  // Coverage: X masking and unmasking cases
  cx_masked:   cover property ( (A===1 && $isunknown({B,C})) && Y===0 );
  cx_unmasked: cover property ( (A===0 && B===0 && C===1'bx) && Y===1'bx );

endmodule

bind sky130_fd_sc_lp__nor3 sky130_fd_sc_lp__nor3_sva_bind sva();

`endif // SKY130_FD_SC_LP__NOR3_SVA