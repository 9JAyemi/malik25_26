// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): cnt_100M, cnt_core, cnt_bsr, check_core_matches_cnt100m, assert, property, posedge, d100_000_000, check_bsr_matches_cntcore, d256, check_pr_matches_cntbsr, d64, check_pr_implies_bsr, check_pr_implies_core, check_bsr_implies_core, check_bsr_increments_when_core_high, past, b1, check_pr_increments_when_core_high, check_pr_increments_when_bsr_high, check_cntcore_increments_when_core_high, d1, check_cntbsr_increments_when_bsr_high, check_cnt100m_increments_when_core_high, check_core_low_next_when_core_high, b0, check_bsr_low_next_when_bsr_high, check_pr_low_next_when_pr_high
bind sequence_counter sequence_counter_sva auto_sva_inst (
    .slowest_sync_clk(slowest_sync_clk),
    .lpf_int(lpf_int),
    .Core(Core),
    .bsr(bsr),
    .pr(pr)
);
