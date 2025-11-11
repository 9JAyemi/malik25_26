// SVA checker for sky130_fd_sc_hvl__inv
module sky130_fd_sc_hvl__inv_sva (
  input  logic A,
  input  logic Y,
  input  logic not0_out_Y,
  input  logic VPWR, VGND, VPB, VNB
);
  default clocking cb @(posedge A or negedge A or posedge Y or negedge Y); endclocking

  // Power rails must be correct
  ap_pwr_good:        assert property (VPWR===1'b1 && VPB===1'b1 && VGND===1'b0 && VNB===1'b0);

  // Functional truth table (when A is known)
  ap_inv_func:        assert property (!$isunknown(A) |-> (Y === ~A));
  ap_no_x_y_when_a:   assert property (!$isunknown(A) |-> !$isunknown(Y));

  // Unknown propagation
  ap_xprop_y:         assert property ($isunknown(A) |-> $isunknown(Y));

  // Internal stage checks
  ap_buf_transparent: assert property (Y === not0_out_Y);
  ap_not_func:        assert property (!$isunknown(A) |-> (not0_out_Y === ~A));
  ap_not_xprop:       assert property ($isunknown(A) |-> $isunknown(not0_out_Y));

  // Edge relationships
  ap_rise_fall:       assert property ($rose(A) |-> $fell(Y));
  ap_fall_rise:       assert property ($fell(A) |-> $rose(Y));

  // Y should never be Z when A is known
  ap_no_z_y:          assert property (!$isunknown(A) |-> (Y !== 1'bz));

  // Coverage
  cp_a0_y1:           cover  property (A===1'b0 && Y===1'b1);
  cp_a1_y0:           cover  property (A===1'b1 && Y===1'b0);
  cp_rise_fall:       cover  property ($rose(A) && $fell(Y));
  cp_fall_rise:       cover  property ($fell(A) && $rose(Y));
  cp_xprop:           cover  property ($isunknown(A) && $isunknown(Y));
endmodule

// Bind into the DUT
bind sky130_fd_sc_hvl__inv sky130_fd_sc_hvl__inv_sva inv_sva_i (
  .A(A), .Y(Y), .not0_out_Y(not0_out_Y),
  .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB)
)