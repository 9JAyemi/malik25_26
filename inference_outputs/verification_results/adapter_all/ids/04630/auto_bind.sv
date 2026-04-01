// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_clk2_matches_cnt_msb, assert, property, disable, iff, check_tgc_reset_on_next_cycle, check_old_clk2_reset_on_next_cycle, check_tgc_low_after_reset_cycle, past, check_old_clk2_low_after_reset_cycle, check_clk2_low_after_reset_cycle, check_cnt_zero_after_reset_cycle, check_tgc_high_only_on_rise, check_tgc_high_only_when_not_reset, check_old_clk2_set_on_clk2_rise, rose, check_old_clk2_clear_on_clk2_fall, fell
bind timer timer_sva auto_sva_inst (
    .wb_clk_i(wb_clk_i),
    .wb_rst_i(wb_rst_i),
    .wb_tgc_o(wb_tgc_o),
    .res(res),
    .cnt(cnt),
    .old_clk2(old_clk2),
    .clk2(clk2),
    .posedge(posedge),
    .b0(b0)
);
