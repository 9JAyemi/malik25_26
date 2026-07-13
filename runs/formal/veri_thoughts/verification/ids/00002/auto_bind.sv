// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_sum_matches_adder, assert, property, posedge, disable, iff, check_overflow_matches_expression, check_indicator_matches_overflow, check_no_overflow_with_opposite_sign_inputs, check_overflow_requires_same_input_signs, check_overflow_requires_result_sign_change, check_positive_overflow_case, check_negative_overflow_case
bind adder top_module_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .a(a),
    .b(b),
    .s(s),
    .overflow(overflow),
    .overflow_detected(overflow_detected),
    .b0(b0),
    .b1(b1)
);
