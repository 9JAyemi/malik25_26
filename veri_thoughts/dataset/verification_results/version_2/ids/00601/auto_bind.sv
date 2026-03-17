// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_count, assert, property, posedge, d0, check_continuous_reset_holds_zero, past, stable, check_deassert_reset_en0_keeps_zero, fell, b0, check_deassert_reset_en1_sets_one, b1, d1, check_increment_when_en_high, disable, iff, check_hold_when_en_low, check_wrap_on_max, hF, check_change_requires_en_and_plus1, changed, check_two_consecutive_en_increments_by2, d2, check_en_then_hold_advances_by1, check_two_cycles_no_en_no_change
bind synchronous_counter synchronous_counter_sva auto_sva_inst (
    .clk(clk),
    .rst(rst),
    .en(en),
    .count(count)
);
