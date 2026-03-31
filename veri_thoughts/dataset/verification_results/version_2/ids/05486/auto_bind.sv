// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_ready_passthrough, assert, property, disable, iff, check_valid_b_reset_low, check_valid_b_sets_after_valid_a, b1, check_valid_b_clears_after_invalid_a, check_data_out_bitwise_or_bits, check_data_out_logical_or_bit, b000, check_logical_bit_matches_bitwise_nonzero, check_accumulator_low_bits_reset_zero, check_accumulator_low_bits_hold_when_invalid, past, check_accumulator_low_bits_add_when_valid
bind bitwise_or top_module_sva auto_sva_inst (
    .clk(clk),
    .rst_n(rst_n),
    .a(a),
    .b(b),
    .data_in(data_in),
    .valid_a(valid_a),
    .ready_b(ready_b),
    .ready_a(ready_a),
    .valid_b(valid_b),
    .data_out(data_out),
    .posedge(posedge),
    .b0(b0)
);
