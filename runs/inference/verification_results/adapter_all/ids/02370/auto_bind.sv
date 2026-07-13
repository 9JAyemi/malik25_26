// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_clears_next, assert, property, posedge, b0000, b0, inc_when_enabled_not_max, disable, iff, hF, past, d1, wrap_when_enabled_at_max, h0, b1, hold_when_disabled, overflow_implies_prev_enable_and_max, overflow_single_cycle_pulse, overflow_implies_next_count_zero, overflow_implies_count_zero_now, zero_count_implies_prev_max_no_reset, zero_count_stays_zero_after_reset
bind counter counter_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .enable(enable),
    .count(count),
    .overflow(overflow)
);
