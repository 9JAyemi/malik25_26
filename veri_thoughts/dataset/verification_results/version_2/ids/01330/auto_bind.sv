// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_outputs_zero, assert, property, h0, check_count_load_next, disable, iff, past, check_sum_load_next, hF, check_sum_stable_no_load, check_sum_change_implies_prev_load, check_count_inc_when_up, d1, check_count_dec_when_down, check_sum_zero_after_reset_release, check_count_back_to_back_loads
bind up_down_counter top_module_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .up_down(up_down),
    .load(load),
    .data_in(data_in),
    .count(count),
    .sum(sum),
    .posedge(posedge)
);
