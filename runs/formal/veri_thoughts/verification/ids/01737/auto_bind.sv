// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): counter, check_match_resets_and_toggles, assert, property, posedge, d0, past, check_no_match_increments_and_holds, d1, check_toggle_only_on_match, check_toggle_implies_counter_zero, check_zero_next_implies_match_or_overflow, hF, check_overflow_wrap_and_hold, check_match_blocks_increment_when_not_max, check_counter_update_form, b1
bind clock_phase_shifter clock_phase_shifter_sva auto_sva_inst (
    .clk(clk),
    .phase_shift_amount(phase_shift_amount),
    .clk_phase_shifted(clk_phase_shifted)
);
