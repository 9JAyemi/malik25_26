// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): count, mux_out, reset_clears_count_next, assert, property, posedge, h0, count_zero_while_reset, past, count_is_one_after_release, disable, iff, h1, count_increments_no_wrap, hF, d1, count_wrap_after_max, mux_sel0_out_eq_in1, mux_sel1_out_eq_in2, mux_equal_inputs_passthrough, mux_out_stable_when_inputs_stable, stable, out_is_xor_of_count_and_mux, out_equals_count_when_mux_zero, out_equals_not_count_when_mux_all_ones, out_stable_when_inputs_stable
bind counter_mux_xor counter_mux_xor_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .mux_in1(mux_in1),
    .mux_in2(mux_in2),
    .select(select),
    .out(out)
);
