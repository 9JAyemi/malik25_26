// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_vpwr_const_high, assert, property, posedge, disable, iff, b1, check_vgnd_const_low, b0, check_post_reset_body_bias_low, past, check_vnb_forced_low_every_cycle, check_disable_clears_body_bias, check_enable_keeps_vnb_low
bind voltage_supply voltage_supply_sva auto_sva_inst (
    .clk(clk),
    .rst(rst),
    .enable(enable),
    .VPWR(VPWR),
    .VGND(VGND),
    .VPB(VPB),
    .VNB(VNB)
);
