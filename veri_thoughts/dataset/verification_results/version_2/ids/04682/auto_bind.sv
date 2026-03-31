// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_toggle_update_when_ce_high, assert, property, past, check_toggle_hold_when_ce_low, check_sync_shift_when_ce_high, check_sync_hold_when_ce_low, check_flag_out_is_xor, check_flag_out_updates_from_prior_sync_stages, check_flag_out_holds_when_ce_low
bind flag_domain_crossing_ce flag_domain_crossing_ce_sva auto_sva_inst (
    .CLK_A(CLK_A),
    .CLK_A_CE(CLK_A_CE),
    .CLK_B(CLK_B),
    .CLK_B_CE(CLK_B_CE),
    .FLAG_IN_CLK_A(FLAG_IN_CLK_A),
    .FLAG_OUT_CLK_B(FLAG_OUT_CLK_B),
    .FLAG_TOGGLE_CLK_A(FLAG_TOGGLE_CLK_A),
    .SYNC_CLK_B(SYNC_CLK_B),
    .posedge(posedge)
);
