// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): q_reg, sum, check_q_mirrors_sum, assert, property, negedge, disable, iff, check_sum_lsb_is_parity, check_sum_upper_zero, d0, check_q_upper_zero, check_q_range_is_0_or_1, d1, check_qreg_updates_from_prev_d_masked, past, check_next_q_lsb_matches_prev_masked_d, check_all_resets_clear_q, genvar, i_rst, generate, for, begin, gen_reset_clear, check_reset_high_clears_qreg, b0, end, endgenerate, i_cap, gen_capture, check_capture_d_when_reset_low
bind flipflop_adder flipflop_adder_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .d(d),
    .q(q)
);
