// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_outputs_cleared, assert, property, posedge, h00, b0, valid_only_when_not_in_reset, check_add_result, disable, iff, past, b00, check_sub_result, b01, check_mul_result, b10, check_div_result_nonzero, b11, stable_result_when_inputs_stable, stable, mul_by_zero_yields_zero, add_with_b_zero_identity, sub_with_b_zero_identity, div_by_one_identity, h01
bind calculator calculator_sva auto_sva_inst (
    .rst(rst),
    .clk(clk),
    .a(a),
    .b(b),
    .op(op),
    .result(result),
    .valid(valid)
);
