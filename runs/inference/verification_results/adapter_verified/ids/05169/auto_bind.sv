// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): cnt_100M, cnt_core, cnt_bsr, check_core_high_when_cnt_100M_max, assert, property, posedge, disable, iff, b0, d100_000_000, b1, check_core_low_when_cnt_100M_not_max, check_bsr_high_when_core_and_cnt_core_max, d255, check_bsr_low_when_core_low_or_cnt_core_not_max, check_pr_high_when_bsr_and_cnt_bsr_max, d63, check_pr_low_when_bsr_low_or_cnt_bsr_not_max
bind sequence_counter sequence_counter_sva auto_sva_inst (
    .slowest_sync_clk(slowest_sync_clk),
    .lpf_int(lpf_int),
    .Core(Core),
    .bsr(bsr),
    .pr(pr)
);
