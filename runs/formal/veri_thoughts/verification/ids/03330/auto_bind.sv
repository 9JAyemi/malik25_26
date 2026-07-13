// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): clk, check_ripple_low_add, assert, property, posedge, check_ripple_high_add, check_carry_select_lower_half, check_carry_select_upper_half, d1, check_decoder_upper_byte, check_decoder_lower_byte, check_functional_product, h00, h00ff, check_output_select_product, check_output_select_decoder_low_byte, check_output_mux_behavior
bind top_module top_module_sva auto_sva_inst (
    .a(a),
    .b(b),
    .select(select),
    .out(out),
    .sum(sum),
    .upper_byte(upper_byte),
    .lower_byte(lower_byte),
    .product(product),
    .sum_low(sum_low),
    .sum_high(sum_high),
    .carry_out_low(carry_out_low),
    .carry_out_high(carry_out_high)
);
