// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): past_valid, if, b0, else, b1, check_rising_edge_equals_sum_output, assert, property, disable, iff, check_sum_output_equals_q_plus_d, check_rising_edge_equals_q_plus_d, check_sum_minus_d_equals_q, check_sum_minus_q_equals_d, check_sum_stable_when_q_and_d_stable, stable, check_rising_stable_when_q_and_d_stable, check_q_exact_update, past, check_q_no_new_ones, h00, check_q_zero_on_mismatch_bits, check_q_hold_on_match_bits
bind rising_edge_detection top_module_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .d(d),
    .in(in),
    .q(q),
    .rising_edge(rising_edge),
    .sum_output(sum_output),
    .always(always),
    .posedge(posedge),
    .begin(begin),
    .end(end)
);
