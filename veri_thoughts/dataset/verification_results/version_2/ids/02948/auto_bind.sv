// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): counter, speaker, slow_rate_old, check_speaker_out_matches_speaker, assert, property, posedge, check_rate_change_resets_and_captures, d0, b0, past, check_zero_rate_forces_idle, check_increment_and_hold_speaker_while_counting, d1, check_toggle_and_reset_on_match, check_slow_rate_old_stable_without_change, check_counter_bounded_when_rate_stable, check_idle_invariant_while_zero_and_stable
bind pwm_controller pwm_controller_sva auto_sva_inst (
    .clk(clk),
    .slow_rate(slow_rate),
    .speaker_out(speaker_out)
);
