// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): charge_pump_out, loop_filter_out, vco_out, div_by_2_out, reset_c0_low, assert, property, b0, reset_phase_error_d1_zero, reset_charge_pump_zero, h00, reset_loop_filter_zero, h0000, reset_vco_zero, h00000000, reset_div2_zero, comb_phase_error_def, disable, iff, pipe_phase_error_d1, past, cp_nextstate_match, h7F, d1, h80, cp_step_bound, lf_accumulate, vco_accumulate, c0_matches_div2_msb
bind de_PLL de_PLL_sva auto_sva_inst (
    .areset(areset),
    .inclk0(inclk0),
    .c0(c0),
    .phase_error(phase_error),
    .phase_error_d1(phase_error_d1),
    .posedge(posedge)
);
