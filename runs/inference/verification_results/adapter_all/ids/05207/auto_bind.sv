// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_forces_zero, assert, property, posedge, d0, count_one_on_reset_release, rose, d1, count_increments_when_not_reset, disable, iff, past, count_changes_each_cycle, count_wraps_from_max, hF, h0, zero_implies_prev_max, one_implies_prev_zero, h1, two_implies_prev_one, h2, max_implies_prev_min, he, min_implies_next_max
bind sync_reset_counter sync_reset_counter_sva auto_sva_inst (
    .clk(clk),
    .rst(rst),
    .count(count)
);
