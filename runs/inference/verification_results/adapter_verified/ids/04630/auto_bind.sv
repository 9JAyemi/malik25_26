// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_tgc, assert, property, check_tgc_low_during_reset, check_tgc_high_on_parity_change, disable, iff, past, b1, check_tgc_low_on_parity_same, check_tgc_rise_requires_parity_change, rose, check_tgc_fall_requires_parity_same, fell
bind timer timer_sva auto_sva_inst (
    .wb_clk_i(wb_clk_i),
    .wb_rst_i(wb_rst_i),
    .wb_tgc_o(wb_tgc_o),
    .cnt(cnt),
    .old_clk2(old_clk2),
    .posedge(posedge),
    .b0(b0)
);
