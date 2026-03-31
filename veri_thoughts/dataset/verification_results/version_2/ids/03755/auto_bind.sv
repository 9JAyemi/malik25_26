// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_output_matches_masked_add, assert, property, posedge, disable, iff, b0, b1, check_carry_matches_addition, h0ff, check_low_byte_matches_and_of_sum, check_low_byte_subset_of_input_and, h00, check_zero_operand_gives_zero_output, h000, check_all_ones_corner_case, hff, h1fe
bind binary_adder top_module_assertions auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .a(a),
    .b(b),
    .sum_and_carry(sum_and_carry)
);
