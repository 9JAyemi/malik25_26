// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_sets_zero_next, assert, property, posedge, d0, check_reset_holds_zero, past, check_reset_overrides_load, check_load_updates_count, disable, iff, check_increment_when_idle, d1, check_double_idle_increments_by_two, d2, check_wraparound_from_15, hF, h0, check_consecutive_load_same_data_holds_count, check_post_reset_count_zero, fell, check_next_state_matches_rtl, b1
bind binary_counter binary_counter_sva auto_sva_inst (
    .reset(reset),
    .load(load),
    .clk(clk),
    .data_in(data_in),
    .count(count)
);
