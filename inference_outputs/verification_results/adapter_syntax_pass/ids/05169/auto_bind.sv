// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): cnt_100M, cnt_core, cnt_bsr, check_core_matches_100m_count, assert, property, posedge, d100000000, check_core_is_single_cycle, check_core_only_after_wrap, d0, check_core_only_after_99999999, past, d99999999, check_core_not_back_to_back, check_core_not_on_zero_count, check_bsr_matches_core_count, d256, check_pr_matches_bsr_count, d64, check_pr_is_single_cycle, check_pr_only_after_wrap, check_pr_only_after_63, d63, check_pr_not_back_to_back, check_pr_not_on_zero_count
bind sequence_counter sequence_counter_sva auto_sva_inst (
    .slowest_sync_clk(slowest_sync_clk),
    .lpf_int(lpf_int),
    .Core(Core),
    .bsr(bsr),
    .pr(pr)
);
