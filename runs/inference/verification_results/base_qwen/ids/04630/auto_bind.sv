// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): counter_increments, assert, property, disable, iff, clk2_assignment, wb_tgc_o_assertion, rose, b1, wb_tgc_o_deassertion, fell, wb_tgc_o_reset, wb_tgc_o_when_clk2_zero, wb_tgc_o_when_clk2_one, counter_wraparound, clk2_delayed, wb_tgc_o_when_old_clk2_one_clk2_zero
bind timer timer_sva auto_sva_inst (
    .wb_clk_i(wb_clk_i),
    .wb_rst_i(wb_rst_i),
    .wb_tgc_o(wb_tgc_o),
    .posedge(posedge),
    .cnt(cnt),
    .phase(phase),
    .clk2(clk2),
    .res(res),
    .b0(b0),
    .old_clk2(old_clk2)
);
