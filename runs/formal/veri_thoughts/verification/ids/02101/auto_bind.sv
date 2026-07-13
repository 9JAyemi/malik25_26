// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): clk, check_mode00_sum_and_zeros, assert, property, posedge, b00, sd0, check_mode01_diff_and_zeros, b01, check_mode10_prod_and_zeros, b10, check_mode11_zeros, b11, check_mode11_quotient_value, check_sum_zero_when_not_mode00, check_difference_zero_when_not_mode01, check_product_zero_when_not_mode10, check_quotient_zero_when_not_mode11, check_outputs_at_most_one_nonzero
bind simple_calculator simple_calculator_sva auto_sva_inst (
    .a(a),
    .b(b),
    .mode(mode),
    .sum(sum),
    .difference(difference),
    .product(product),
    .quotient(quotient)
);
