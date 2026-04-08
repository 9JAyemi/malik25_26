// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_outputs, assert, property, b0000, check_sum_matches_previous_inputs, disable, iff, past, check_cout_matches_previous_inputs, check_a_passthrough_when_b_and_cin_zero, check_b_passthrough_when_a_and_cin_zero, check_zero_inputs_produce_zero_outputs, check_cout_high_for_msb_pair, b1, check_cout_low_for_zero_msb_inputs
bind four_bit_adder four_bit_adder_sva auto_sva_inst (
    .clk(clk),
    .rst(rst),
    .a(a),
    .b(b),
    .cin(cin),
    .sum(sum),
    .cout(cout),
    .posedge(posedge),
    .b0(b0)
);
