// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_state, assert, property, posedge, h0, b0, check_count_increments_when_enabled, disable, iff, hF, past, d1, check_count_wraps_at_max, check_overflow_low_when_incrementing, check_overflow_asserts_at_max, b1, check_count_holds_when_disabled, check_overflow_holds_when_disabled
bind counter counter_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .enable(enable),
    .count(count),
    .overflow(overflow)
);
