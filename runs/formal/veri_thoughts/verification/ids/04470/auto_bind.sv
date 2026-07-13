// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_power_ok_matches_and, assert, property, global_clock, check_power_ok_implies_vpwr, check_power_ok_implies_vpb, check_low_vpwr_forces_power_not_ok, check_low_vpb_forces_power_not_ok, check_vgnd_unused, initstate, changed, stable, check_vnb_unused
bind power_check power_check_sva auto_sva_inst (
    .VPWR(VPWR),
    .VGND(VGND),
    .VPB(VPB),
    .VNB(VNB),
    .power_ok(power_ok)
);
