// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_add_operation, assert, property, global_clock, b00, check_sub_operation, b01, check_sub_borrow_flag, check_and_operation, b10, b0, check_default_outputs, b11, b0000, check_outputs_stable_when_inputs_stable, stable, check_sub_equal_operands_zero_result, check_and_zero_operand_zero_result, check_and_result_subset_inputs
bind simple_arithmetic_unit simple_arithmetic_unit_sva auto_sva_inst (
    .a(a),
    .b(b),
    .op_select(op_select),
    .result(result),
    .carry_borrow(carry_borrow)
);
