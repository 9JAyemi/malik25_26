// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_upper_byte_reset_zero, assert, property, h00, check_lower_byte_reset_zero, check_final_output_reset_zero, check_upper_byte_captures_input, disable, iff, initstate, past, check_lower_byte_captures_input, check_xor_output_matches_inputs, check_final_output_uses_prior_xor_and_lower, check_final_output_equals_prior_upper_byte
bind top_module top_module_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .in(in),
    .final_output(final_output),
    .upper_byte(upper_byte),
    .lower_byte(lower_byte),
    .xor_output(xor_output),
    .posedge(posedge)
);
