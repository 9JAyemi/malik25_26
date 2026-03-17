// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_sum_is_xor, assert, property, disable, iff, check_carry_is_and, check_sum_and_carry_mutex, b0, check_carry_subset_of_a, check_carry_subset_of_b, check_sum_xor_carry_eq_or, check_sum_or_carry_eq_or, check_recover_b_from_sum_a, check_recover_a_from_sum_b, check_stability_when_inputs_stable, stable, check_sum_and_a_mask, check_sum_and_b_mask
bind dff_with_reset top_module_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .a(a),
    .b(b),
    .sum(sum),
    .carry_out(carry_out),
    .posedge(posedge)
);
