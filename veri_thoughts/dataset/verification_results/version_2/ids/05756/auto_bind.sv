// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): register_a, register_b, register_p, check_decoder_select_00, assert, property, disable, iff, check_decoder_select_01, check_decoder_select_10, check_decoder_select_11, check_booth_output_matches_register_p, check_top_reset_clears_product, check_booth_reset_clears_state, check_top_product_captures_booth_output, b1, past, check_register_b_captures_b, check_register_a_shifts_previous_value, check_register_p_add_on_00, check_register_p_sub_on_01, check_register_p_add_on_10
bind top_module top_module_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .a(a),
    .b(b),
    .select(select),
    .product(product),
    .booth_input(booth_input),
    .booth_output(booth_output),
    .posedge(posedge),
    .b00(b00),
    .b0001(b0001),
    .b01(b01),
    .b0010(b0010),
    .b10(b10),
    .b0100(b0100),
    .b11(b11),
    .b1000(b1000),
    .b0(b0),
    .b0000(b0000)
);
