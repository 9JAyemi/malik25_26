// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_outputs, assert, property, posedge, d0, b0, check_count_holds_when_disabled, disable, iff, stable, check_max_flag_holds_when_disabled, check_wrap_and_flag_at_max, d15, b1, check_non_wrap_clears_flag, check_load_set_value_when_different, past, check_increment_when_set_matches_count, d1
bind counter counter_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .enable(enable),
    .set_value(set_value),
    .count(count),
    .max_value_reached(max_value_reached)
);
