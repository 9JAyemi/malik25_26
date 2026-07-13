// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_full_addition, assert, property, posedge, disable, iff, b0, check_carry_out_matches_overflow, h10000, check_zero_b_identity, h0000, check_zero_a_identity, check_lsb_full_adder_relation, check_upper_byte_without_low_carry, h100, check_upper_byte_with_low_carry, b1
bind eight_bit_adder sixteen_bit_adder_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .a(a),
    .b(b),
    .carry_in(carry_in),
    .sum(sum),
    .carry_out(carry_out)
);
