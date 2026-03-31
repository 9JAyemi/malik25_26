// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_state, assert, property, check_reset_clears_jc_out, check_jc_decode_known_states, disable, iff, inside, check_jc_decode_default_zero, check_zero_state_sticky, check_binary_vector_copy, check_msb_output_matches_input, check_mid_output_matches_input, check_lsb_output_matches_input, check_functional_or_result, check_zero_state_top_output, check_reset_top_output
bind johnson_counter top_module_sva auto_sva_inst (
    .clk(clk),
    .rst_n(rst_n),
    .in_vec(in_vec),
    .out_vec(out_vec),
    .msb_out(msb_out),
    .mid_out(mid_out),
    .lsb_out(lsb_out),
    .jc_out(jc_out),
    .bn_out(bn_out),
    .state(state),
    .posedge(posedge),
    .b00000000(b00000000),
    .b10000000(b10000000),
    .b11000000(b11000000),
    .b11100000(b11100000),
    .b11110000(b11110000),
    .b01111000(b01111000),
    .b00111100(b00111100),
    .b00011110(b00011110),
    .b00001111(b00001111),
    .b0000(b0000)
);
