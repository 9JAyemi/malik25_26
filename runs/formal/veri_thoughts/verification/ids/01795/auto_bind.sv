// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_counter_reset_next_zero, assert, property, disable, iff, past, d0, check_counter_increment, d1, check_counter_wrap_to_zero_on_match, check_adder_add_mode, check_adder_sub_mode, check_q_load_prev_count_on_select1, check_q_load_prev_out_on_select0, check_q_steps_like_counter_when_select_held, check_q_wrap_when_select_held, check_q_inc_when_select_held_not_at_N
bind counter top_module_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .N(N),
    .B(B),
    .mode(mode),
    .select(select),
    .q(q),
    .posedge(posedge),
    .counter_inst(counter_inst),
    .count_out(count_out),
    .adder_subtractor_inst(adder_subtractor_inst),
    .out(out)
);
