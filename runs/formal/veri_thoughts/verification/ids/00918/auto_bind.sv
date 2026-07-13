// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_outputs_zero, assert, property, posedge, b000, b0, hold_when_disabled, disable, iff, past, increment_when_enabled, b111, b001, wrap_and_set_flag, b1, flag_implies_count_zero, flag_rise_on_wrap_only, rose, count_change_requires_enable, flag_change_requires_enable, clear_flag_on_enable_from_zero, enabled_step_changes_count
bind counter_3bit_sync_reset counter_3bit_sync_reset_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .ena(ena),
    .count(count),
    .flag(flag)
);
