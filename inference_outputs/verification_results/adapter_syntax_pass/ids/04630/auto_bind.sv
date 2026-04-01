// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_clk2_matches_cnt_msb, assert, property, disable, iff, check_old_clk2_captures_clk2, b1, past, check_cnt_increments_by_phase, check_wb_tgc_o_asserts_on_first_clk2_rise, check_wb_tgc_o_deasserts_on_next_clk2_fall, check_wb_tgc_o_low_after_reset
bind timer timer_sva auto_sva_inst (
    .wb_clk_i(wb_clk_i),
    .wb_rst_i(wb_rst_i),
    .wb_tgc_o(wb_tgc_o),
    .res(res),
    .cnt(cnt),
    .old_clk2(old_clk2),
    .clk2(clk2),
    .posedge(posedge),
    .phase(phase),
    .b0(b0)
);
