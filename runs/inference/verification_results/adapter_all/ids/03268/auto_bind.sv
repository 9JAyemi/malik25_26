// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_clears_count, assert, property, posedge, b0000, count_increments_when_enabled, disable, iff, past, d1, count_holds_when_disabled, count_change_requires_enable_or_reset, reset_priority_over_enable, zero_count_cause, hF, wrap_from_max_when_enabled, h0, hold_at_max_when_disabled, zero_without_reset_implies_prev_wrap, count_change_is_nonzero
bind binary_counter binary_counter_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .enable(enable),
    .count(count)
);
