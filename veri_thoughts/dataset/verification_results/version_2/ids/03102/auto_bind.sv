// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_y_matches_sign_bit, assert, property, global_clock, check_negative_out_is_twos_comp, check_nonnegative_out_is_zero_extended_x, b00, check_encode_eff_0001_to_x0, d0, check_encode_eff_0010_to_x1, d1, check_encode_eff_0100_to_x2, d2, check_encode_eff_1000_to_x3, d3, check_encode_non_onehot_defaults_to_x3, check_sum_matches_out_plus_x, b0, check_sum_msb_is_zero
bind priority_encoder_twos_complement top_module_assertions auto_sva_inst (
    .in(in),
    .X(X),
    .Y(Y),
    .out(out),
    .sum(sum),
    .b0001(b0001),
    .b0010(b0010),
    .b0100(b0100),
    .b1000(b1000)
);
