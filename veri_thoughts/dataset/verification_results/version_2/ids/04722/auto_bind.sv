// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): clk, check_empty_pass_through, assert, property, posedge, b000, check_nonempty_count0_returns_31, d0, d31, check_nonempty_count1_returns_0, d1, check_nonempty_count2_ge2_returns_1, d2, check_nonempty_count2_no_ge2_returns_0, check_nonempty_count3_ge3_returns_2, d3, check_nonempty_count3_ge2_only_returns_1, check_nonempty_count3_no_free_threshold_returns_0
bind fifo_counter fifo_counter_assertions auto_sva_inst (
    .empty(empty),
    .ge2_free(ge2_free),
    .ge3_free(ge3_free),
    .input_tm_cnt(input_tm_cnt),
    .fifo_cnt_inc(fifo_cnt_inc)
);
