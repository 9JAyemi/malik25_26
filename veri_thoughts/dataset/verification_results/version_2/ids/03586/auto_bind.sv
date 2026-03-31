// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): A_reg, B_reg, stage, A_next, B_next, EQ_next, GT_next, LT_next, check_stage0_captures_inputs, assert, property, posedge, d0, d1, past, check_stage1_sorts_registers, d2, check_stage2_returns_to_stage0, check_invalid_stage_holds_state, check_outputs_low_outside_stage2, b0, check_stage2_outputs_match_register_relation, check_lt_output_always_low, check_a_next_is_max_of_registers, check_b_next_is_min_of_registers, check_compare_next_flags_match_relation
bind magnitude_comparator_4bit magnitude_comparator_4bit_assertions auto_sva_inst (
    .A(A),
    .B(B),
    .clk(clk),
    .EQ(EQ),
    .GT(GT),
    .LT(LT)
);
