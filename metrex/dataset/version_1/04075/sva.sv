// SVA for sky130_fd_sc_lp__invkapwr
// Bind these assertions to every instance of the inverter.

module sky130_fd_sc_lp__invkapwr_sva (
  input logic A,
  input logic Y,
  input logic VPWR,
  input logic VGND,
  input logic KAPWR,
  input logic VPB,
  input logic VNB
);

  function automatic bit power_good();
    return (VPWR===1'b1 && KAPWR===1'b1 && VPB===1'b1 &&
            VGND===1'b0 && VNB===1'b0);
  endfunction

  // Supplies must be known and at correct levels
  ap_supplies_known:  assert property (@(VPWR or VGND or KAPWR or VPB or VNB)
                                       !$isunknown({VPWR,VGND,KAPWR,VPB,VNB}));
  ap_supplies_levels: assert property (@(VPWR or VGND or KAPWR or VPB or VNB)
                                       power_good());

  // Functional correctness: for known A, Y is bitwise inversion (no X/Z)
  ap_inv:             assert property (@(A or Y) disable iff (!power_good())
                                       !$isunknown(A) |-> (Y === ~A));

  // X-propagation: unknown A must yield unknown Y
  ap_xprop:           assert property (@(A or Y) disable iff (!power_good())
                                       $isunknown(A) |-> $isunknown(Y));

  // No spurious output activity: Y changes only when A changes
  ap_no_spurious_y:   assert property (@(posedge Y or negedge Y) disable iff (!power_good())
                                       ##0 $changed(A));

  // Zero-delay response: on any A edge, Y updates immediately to ~A
  ap_zero_delay:      assert property (@(posedge A or negedge A) disable iff (!power_good())
                                       ##0 (Y === ~A));

  // Coverage
  cp_A0Y1:            cover property (@(A or Y) disable iff (!power_good())
                                       (A===1'b0 && Y===1'b1));
  cp_A1Y0:            cover property (@(A or Y) disable iff (!power_good())
                                       (A===1'b1 && Y===1'b0));
  cp_toggle_rise:     cover property (@(posedge A) disable iff (!power_good())
                                       ##0 (Y===1'b0));
  cp_toggle_fall:     cover property (@(negedge A) disable iff (!power_good())
                                       ##0 (Y===1'b1));

endmodule

bind sky130_fd_sc_lp__invkapwr
  sky130_fd_sc_lp__invkapwr_sva
    (.A(A), .Y(Y), .VPWR(VPWR), .VGND(VGND), .KAPWR(KAPWR), .VPB(VPB), .VNB(VNB));