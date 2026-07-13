// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_load_updates_count, assert, property, posedge, disable, iff, past, d0, check_load_has_priority_over_count, check_hold_when_idle, check_count_up_wraps_to_zero, check_count_up_increments, d1, check_count_down_wraps_to_max, check_count_down_decrements
bind binary_counter binary_counter_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .count_en(count_en),
    .max_count(max_count),
    .load_val(load_val),
    .load(load),
    .count_dir(count_dir),
    .count_out(count_out)
);
