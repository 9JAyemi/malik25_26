// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_register_reset_value, assert, property, past, check_register_captures_d, disable, iff, check_counter_reset_value, d0, check_counter_increments, d1, check_adder_sum, check_mux_select1, check_mux_select0, check_q_follows_active_output, check_q_select1_sum, check_q_select0_passthrough, check_q_select0_matches_past_d
bind register_module top_module_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .d(d),
    .select(select),
    .q(q),
    .reg_output(reg_output),
    .counter_output(counter_output),
    .active_output(active_output),
    .adder_input(adder_input),
    .posedge(posedge),
    .h34(h34),
    .b0(b0)
);
