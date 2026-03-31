// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_count_resets_to_zero, assert, property, disable, iff, initstate, past, check_count_increments_when_enabled, d1, check_count_holds_when_disabled, check_count_changes_only_with_enable_or_reset, check_count_wraps_from_max, hF, h0, check_compare_matches_relation, check_compare_asserts_on_equal_threshold
bind up_counter_with_comparator top_module_assertions auto_sva_inst (
    .clk(clk),
    .slowena(slowena),
    .reset(reset),
    .threshold(threshold),
    .count(count),
    .high_if_count_greater_than_threshold(high_if_count_greater_than_threshold),
    .posedge(posedge),
    .b0000(b0000)
);
