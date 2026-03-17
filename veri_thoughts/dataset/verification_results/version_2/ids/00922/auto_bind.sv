// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_clears_regs, assert, property, posedge, post_reset_regs_zero, past, check_gray_a_comb, disable, iff, check_gray_b_comb, check_comb_multiplier, check_mult_by_zero, check_bin_reg_tracks_wire, check_bin_reg_eq_past_mult, check_gray_product_prev_grayxor, check_gray_product_prev_func
bind binary_multiplier top_module_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .a(a),
    .b(b),
    .gray_product(gray_product),
    .binary_product(binary_product),
    .binary_product_reg(binary_product_reg),
    .gray_a(gray_a),
    .gray_b(gray_b),
    .b0(b0)
);
