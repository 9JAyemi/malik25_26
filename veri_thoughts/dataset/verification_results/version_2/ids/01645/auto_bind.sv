// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_count1_resets_to_zero, assert, property, check_count1_load_clears, disable, iff, check_count1_inc_when_no_reset_load, past, d1, check_count2_load_clears, check_count2_inc_when_up_no_load, check_count2_dec_when_down_no_load, check_sum_matches_truncated_add, h0FF, check_data_out_eq_sum, check_sum_advances_by_two_on_up, d2, check_sum_stable_on_down
bind up_counter_with_reset_and_load top_module_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .load(load),
    .up_down(up_down),
    .data_in(data_in),
    .data_out(data_out),
    .count1(count1),
    .count2(count2),
    .sum(sum),
    .posedge(posedge),
    .d0(d0)
);
