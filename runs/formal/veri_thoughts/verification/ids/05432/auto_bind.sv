// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): clk, check_add_mode_full_sum, assert, property, posedge, b0, check_invert_b_mode_full_sum, check_lsb_sum_bit, check_add_zero_b_identity, check_add_zero_a_identity, check_add_all_ones_b_wrap, b1, check_invert_b_equal_operands_with_carry_cancel, check_invert_b_equal_operands_without_carry_all_ones, check_invert_b_zero_b_with_carry_identity, check_invert_b_all_ones_b_without_carry_identity, g_width1, check_single_bit_carry_formula
bind fadder fadder_sva auto_sva_inst (
    .WIDTH(WIDTH),
    .a(a),
    .b(b),
    .sub_enable(sub_enable),
    .carry_in(carry_in),
    .res(res),
    .carry_out(carry_out),
    .generate(generate),
    .if(if),
    .begin(begin)
);
