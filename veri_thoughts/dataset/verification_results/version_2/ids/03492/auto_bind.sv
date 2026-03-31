// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_outputs_zero_when_pipelined_enable_low, assert, property, posedge, initstate, past, b0000, b0, check_out_matches_registered_decoder_or_adder, b0001, b00, check_cout_matches_registered_add_carry, b11, check_decode_sel0_sets_out0, b1, check_decode_sel1_sets_out1, b01, check_decode_sel2_sets_upper_pattern, b10, check_decode_sel3_sets_upper_pattern, check_upper_bits_zero_without_upper_decode, check_low_bits_follow_add_when_no_low_decode
bind decoder_2to4_adder decoder_2to4_adder_sva auto_sva_inst (
    .clk(clk),
    .in(in),
    .ena(ena),
    .cin(cin),
    .out(out),
    .cout(cout)
);
