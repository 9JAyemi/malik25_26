// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_clears_sum_next, assert, property, h0000, reset_holds_sum_zero_while_asserted, past, reset_release_preserves_zero, fell, sum_matches_prev_calc, disable, iff, h00, sum_low_byte_matches_prev_calc, sum_high_byte_matches_prev_calc, sum_equals_prev_product_when_c_zero, sum_equals_prev_c_when_a_zero, sum_equals_prev_c_when_b_zero, sum_equals_prev_b_plus_c_when_a_one, h01, sum_equals_prev_a_plus_c_when_b_one, sum_stable_when_inputs_stable_two_cycles
bind top_module top_module_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .a(a),
    .b(b),
    .c(c),
    .sum(sum),
    .posedge(posedge)
);
