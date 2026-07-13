// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): A_reg, B_reg, check_reset_clears_state, assert, property, global_clock, b0000, b0, check_disable_clears_outputs, disable, iff, check_load_a_updates_a_reg, check_load_b_updates_b_reg, check_equal_compare_outputs, b1, check_greater_compare_outputs, check_less_compare_outputs, check_enabled_outputs_are_onehot, check_eq_implies_equal_state, check_gt_implies_greater_state, check_lt_implies_less_state
bind comparator_4bit comparator_4bit_sva auto_sva_inst (
    .A(A),
    .B(B),
    .reset(reset),
    .enable(enable),
    .load_A(load_A),
    .load_B(load_B),
    .EQ(EQ),
    .GT(GT),
    .LT(LT)
);
