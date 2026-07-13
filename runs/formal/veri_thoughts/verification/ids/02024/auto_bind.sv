// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_counter, assert, property, check_reset_holds_zero, check_q_cnt_follows_d_cnt, disable, iff, b1, past, check_next_on_prev_tick, check_next_on_prev_no_tick, check_monotonic_or_wrap, check_d_cnt_matches_tick_logic, check_tick_single_cycle_next_low, check_tick_not_back_to_back_prev_low, check_tick_implies_next_cnt_zero
bind uart_baud_clk uart_baud_clk_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .baud_clk_tick(baud_clk_tick),
    .q_cnt(q_cnt),
    .d_cnt(d_cnt),
    .posedge(posedge),
    .h0000(h0000),
    .h0001(h0001)
);
