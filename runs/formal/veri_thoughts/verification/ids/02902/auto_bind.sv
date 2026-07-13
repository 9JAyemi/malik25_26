// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): clk, check_functional_spec, assert, property, posedge, d3, d2, d1, d0, check_output_range, inside, check_tm_cnt0_zero, check_tm_cnt1_one, check_tm_cnt2_ge2_true, check_tm_cnt2_ge2_false, check_tm_cnt3_ge3_true, check_tm_cnt3_ge2_only_yields_two, check_tm_cnt3_no_free_yields_one
bind fifo_controller fifo_controller_sva auto_sva_inst (
    .ge2_free(ge2_free),
    .ge3_free(ge3_free),
    .input_tm_cnt(input_tm_cnt),
    .fifo_wrptr_inc(fifo_wrptr_inc)
);
