// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_subcounters_clear_after_reset, assert, property, disable, iff, initstate, past, d0, check_count1_increments_below_max, hF, d1, check_count1_wraps_at_max, h0, check_count2_increments_below_max, check_count2_wraps_at_max, check_top_captures_previous_sum, b0, check_equal_subcounters_stay_equal, check_equal_subcounters_double_into_count, check_top_count_zero_two_cycles_after_reset, check_top_count_within_sum_range, d30
bind counter counter_top_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .count(count),
    .count1(count1),
    .count2(count2),
    .posedge(posedge)
);
