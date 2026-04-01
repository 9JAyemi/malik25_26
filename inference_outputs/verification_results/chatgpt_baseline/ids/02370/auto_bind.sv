// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_clears_outputs_next, assert, property, posedge, h0, b0, hold_when_disabled, disable, iff, past, wrap_sets_overflow_and_zero, hF, b1, increment_when_enabled, d1, no_overflow_on_non_wrap, overflow_implies_count_zero_current, count_changes_when_enabled, outputs_change_only_due_to_enable_or_reset, overflow_rise_corresponds_to_wrap, rose
bind counter counter_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .enable(enable),
    .count(count),
    .overflow(overflow)
);
