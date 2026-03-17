// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): clk, check_add_result_matches_opcode, assert, property, posedge, b00, check_sub_result_matches_opcode, b01, check_mul_result_matches_opcode, b10, check_div_result_matches_opcode_nonzero, b11, d0, check_stable_result_when_inputs_stable, past, check_result_change_implies_input_change, check_add_by_zero_identity, check_sub_by_zero_identity, check_mul_by_zero_identity, check_div_by_one_identity, d1
bind simple_calculator simple_calculator_sva auto_sva_inst (
    .A(A),
    .B(B),
    .opcode(opcode),
    .result(result)
);
