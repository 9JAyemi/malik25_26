// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): CLK, check_x_definition, assert, property, posedge, check_x_implies_all_high, b1, check_all_high_implies_x_high, check_x_low_when_vpwr_low, b0, check_x_low_when_kagnd_low, check_x_low_when_a_low, check_x_low_when_sleepb_low, check_x_stable_when_used_inputs_stable, stable, check_x_unchanged_on_vpb_toggle, changed, check_x_unchanged_on_vnb_toggle
bind pwrgood_pp power_good_checker_sva auto_sva_inst (
    .A(A),
    .SLEEP_B(SLEEP_B),
    .VPWR(VPWR),
    .KAGND(KAGND),
    .VPB(VPB),
    .VNB(VNB),
    .X(X)
);
