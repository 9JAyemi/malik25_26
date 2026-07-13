// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): shift_reg, a_reg, b_reg, product, sum, carry, check_a_reg_captures_a, assert, property, posedge, initstate, past, check_b_reg_captures_b, check_shift_reg_shift_behavior, b0, check_shift_reg_lsb_zero, check_product_definition, check_sum_definition, check_carry_definition, check_s_matches_sum_low_byte, check_overflow_matches_carry, check_overflow_matches_expression
bind shift_adder shift_adder_sva auto_sva_inst (
    .clk(clk),
    .a(a),
    .b(b),
    .s(s),
    .overflow(overflow)
);
