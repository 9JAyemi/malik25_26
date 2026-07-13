// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_forces_zero, assert, property, posedge, b0, b00, count_increments_when_enabled, disable, iff, b11, past, b01, count_wraps_when_enabled_at_max, count_holds_when_disabled, count_change_requires_enable_or_reset, b1, prev_reset_low_implies_count_zero, prev_reset_high_and_enabled_implies_change, prev_reset_high_and_disabled_implies_hold, zero_now_has_valid_prev, one_now_has_valid_prev, b10, two_now_has_valid_prev, three_now_has_valid_prev
bind counter counter_sva auto_sva_inst (
    .clk(clk),
    .rst(rst),
    .en(en),
    .count(count)
);
