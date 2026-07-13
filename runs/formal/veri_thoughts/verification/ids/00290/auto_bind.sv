// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reg1, reg2, counter, check_reset_loads_state, assert, property, posedge, h34, h0, check_reset_sets_result, h3434, check_result_matches_registers, disable, iff, check_q_active_when_select_high, b1, check_q_active_when_select_low, b0, check_reg1_loads_d1_when_selected, past, check_reg1_holds_when_select_low, stable, check_reg2_stable_without_reset, check_counter_stable_without_reset, check_q_active_matches_result_upper_when_selected
bind top_module top_module_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .d1(d1),
    .d2(d2),
    .select(select),
    .q_active(q_active),
    .result(result)
);
