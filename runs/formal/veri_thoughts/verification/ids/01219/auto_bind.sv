// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): hour_count, minute_count, outputs_match_hour, assert, property, posedge, disable, iff, outputs_match_minute, reset_sets_counts, d1, d0, reset_clears_ampm, b0, minute_increments, d59, past, minute_wraps_at_59, hour_holds_when_minute_not_59, hour_increments_on_minute_wrap, d12, hour_wraps_from_12_on_minute_wrap, ampm_toggles_at_hour_12, ampm_holds_when_not_12, valid_high_next_if_12_00, b1, valid_low_next_if_not_12_00
bind digitalclock digitalclock_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .hour(hour),
    .minute(minute),
    .ampm(ampm),
    .valid(valid)
);
