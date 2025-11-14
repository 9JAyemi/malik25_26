// SVA for voltage_supply
module voltage_supply_sva (
  input clk, rst, enable,
  input VPWR, VGND, VPB, VNB
);

  default clocking cb @(posedge clk); endclocking

  // Power rails must be constant and known
  ap_rails_const:      assert property (VPWR === 1'b1 && VGND === 1'b0);
  ap_vnb_zero:         assert property (VNB  === 1'b0);

  // Reset must clear outputs (sampled each clk while rst high)
  ap_rst_clears:       assert property (rst |-> (VPB === 1'b0 && VNB === 1'b0));

  // Ignore functional checks during reset
  default disable iff (rst);

  // When disabled, VPB forced to 0 and stays 0 until enable rises
  ap_vpb_zero_when_dis: assert property ((!enable) |-> (VPB === 1'b0) until_with enable);

  // A change on VPB must be justified by enable in this or previous cycle
  ap_vpb_change_needs_en: assert property ($changed(VPB) |-> (enable || $past(enable)));

  // If enable low for 2+ cycles, VPB must be 0 and stable
  ap_vpb_stable_when_low: assert property ((!enable && !$past(enable)) |-> (VPB === 1'b0 && $stable(VPB)));

  // No X/Z on any outputs after reset released
  ap_no_xz_outputs:    assert property (!$isunknown({VPWR, VGND, VPB, VNB}));

  // Coverage
  cp_reset_pulse:      cover property (rst ##1 !rst);
  cp_en_causes_toggle: cover property (enable [*2] ##[1:$] $changed(VPB));
  cp_dis_forces_zero:  cover property (enable ##1 !enable ##1 VPB === 1'b0);

endmodule

bind voltage_supply voltage_supply_sva sva_i(
  .clk(clk),
  .rst(rst),
  .enable(enable),
  .VPWR(VPWR),
  .VGND(VGND),
  .VPB(VPB),
  .VNB(VNB)
);