// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): clk, check_sum_matches_four_bit_addition, assert, property, posedge, check_control_low_matches_addition, check_control_high_matches_addition, check_lsb_matches_full_adder_equation, check_low_two_bits_match_partial_addition, check_low_three_bits_match_partial_addition, check_zero_b_passthrough, h0, check_zero_a_passthrough, check_control_toggle_does_not_change_sum, disable, iff, initstate, changed, stable, check_stable_inputs_hold_sum
bind adder_mux adder_mux_sva auto_sva_inst (
    .a(a),
    .b(b),
    .control(control),
    .sum(sum)
);
