// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_clears_outputs_next, assert, property, disable, iff, past, d0, b0, reset_has_priority_over_load, load_updates_sum_next, load_updates_sub_next, hold_without_load, change_only_after_load, changed, fsm_c_matches_carry_on_sum, fsm_c_matches_borrow_on_sub
bind Add_Subt Add_Subt_sva auto_sva_inst (
    .clk(clk),
    .rst(rst),
    .load_i(load_i),
    .Add_Sub_op_i(Add_Sub_op_i),
    .Data_A_i(Data_A_i),
    .PreData_B_i(PreData_B_i),
    .Data_Result_o(Data_Result_o),
    .FSM_C_o(FSM_C_o),
    .posedge(posedge)
);
