// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_drives_zero, assert, property, posedge, h0, b0, increment_when_not_max, disable, iff, past, hF, d1, wrap_when_prev_max, b1, flag_rise_only_on_wrap, rose, flag_implies_zero_count, flag_one_cycle_pulse, nonzero_count_implies_flag_zero, zero_now_means_prev_max, count_changes_every_cycle_active, present_max_wraps_next
bind binary_counter binary_counter_sva auto_sva_inst (
    .clk(clk),
    .rst(rst),
    .count(count),
    .max_reached(max_reached)
);
