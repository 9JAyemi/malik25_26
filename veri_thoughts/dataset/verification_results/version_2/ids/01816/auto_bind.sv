// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_counter_load_8_next_on_reset_low, assert, property, b0, check_counter_is_8_after_reset_low, past, check_mux_out_b_when_both_high, disable, iff, hF, check_mux_out_a_otherwise, check_adder_sum_correct, check_adder_sum_both_case, check_adder_sum_a_case, check_out_always_one_cycle_later_high, b1, check_out_always_stable_high, check_adder_conditional_sum_consistency
bind async_reset_binary_counter top_module_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .sel_b1(sel_b1),
    .sel_b2(sel_b2),
    .out_always(out_always),
    .q_counter(q_counter),
    .mux_out(mux_out),
    .adder_out(adder_out),
    .posedge(posedge),
    .b1000(b1000)
);
