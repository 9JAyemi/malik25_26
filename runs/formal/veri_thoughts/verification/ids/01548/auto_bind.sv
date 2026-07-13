// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_out0_matches_past_a_and_b, assert, property, disable, iff, past, check_out1_matches_past_c_and_d, check_out0_requires_past_a_high_for_ones, b00, check_out0_requires_past_b_high_for_ones, check_out0_zero_when_past_a_zero, check_out0_zero_when_past_b_zero, check_out0_masked_by_past_or, check_out1_zero_when_any_past_input_zero, check_out0_stable_when_ab_stable, stable, check_out1_stable_when_cd_stable, check_out1_rise_requires_past_cd_high, rose
bind bm_dag2_log_mod bm_dag2_log_mod_sva auto_sva_inst (
    .clock(clock),
    .reset_n(reset_n),
    .a_in(a_in),
    .b_in(b_in),
    .c_in(c_in),
    .d_in(d_in),
    .out0(out0),
    .out1(out1),
    .posedge(posedge)
);
