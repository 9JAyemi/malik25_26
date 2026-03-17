// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): result_add_correct, assert, property, posedge, b0, result_sub_correct, b1, stable_result_when_inputs_stable, past, result_switch_on_op_rise, result_switch_on_op_fall, overflow_set_when_condition, overflow_clear_when_not_condition, overflow_binary_after_first_cycle, inside, overflow_stable_when_signs_stable
bind calculator calculator_sva auto_sva_inst (
    .a(a),
    .b(b),
    .op(op),
    .clk(clk),
    .result(result),
    .overflow(overflow)
);
