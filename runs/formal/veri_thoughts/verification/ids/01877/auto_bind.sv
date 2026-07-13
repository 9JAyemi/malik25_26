// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_result_next_equals_split_sum, assert, property, b1, past, check_lower16_matches_ll_product, check_upper16_matches_composed_sum, check_result_stable_if_inputs_stable, check_low16_stable_if_low_inputs_stable, check_result_zero_when_operand_zero, d0, check_result_equals_ll_when_high_zero, check_low16_zero_when_any_low_zero, check_upper16_eq_msbprod_low16_when_low_zero
bind mul16 pipelined_multiplier_sva auto_sva_inst (
    .a(a),
    .b(b),
    .enable(enable),
    .result(result),
    .posedge(posedge)
);
