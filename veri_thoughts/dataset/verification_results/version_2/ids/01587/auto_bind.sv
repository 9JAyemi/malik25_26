// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): state, shift_reg, output_reg, IDLE, b00, STATE1, b01, STATE2, b10, PATTERN, b101, check_detected_matches_output_reg, assert, property, posedge, disable, iff, check_reset_release_defaults, past, b000, b0, check_shift_reg_update, check_idle_match_next_state, check_idle_nomatch_next_state, check_state1_next_state, check_state2_next_state, check_idle_match_detected, b1, check_idle_nomatch_detected, check_state1_detected, check_state2_detected, check_detected_two_cycle_pulse, rose, check_detected_rise_corresponds_to_match
bind fsm_pattern_detection fsm_pattern_detection_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .data(data),
    .detected(detected)
);
