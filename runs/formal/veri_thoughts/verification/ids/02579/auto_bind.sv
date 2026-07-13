// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): update_to_zero_on_match, assert, property, posedge, past, h00, update_increment_on_no_match, d1, zero_implies_from_match_or_overflow, hFF, overflow_to_zero_when_prev_ff_no_match, no_spurious_zero_without_ff_no_match, two_cycle_increment_without_match, d2, zero_sticky_when_max_zero, from_zero_when_max_nonzero, h01
bind binary_counter binary_counter_sva auto_sva_inst (
    .clk(clk),
    .max_count(max_count),
    .count(count)
);
