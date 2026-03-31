// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): IDLE, b00, STATE1, b01, STATE2, b10, b11, check_match_high_in_match_state, assert, property, posedge, b1, check_match_low_outside_match_state, b0, check_idle_to_state1_on_0001, b0001, check_idle_stays_idle_on_other_inputs, check_state1_to_state2_on_0000, b0000, check_state1_returns_idle_on_other_inputs, check_state2_to_match_on_0001, check_state2_returns_idle_on_other_inputs, check_match_returns_to_idle, check_match_is_single_cycle_pulse
bind fsm_4bit_sequence_detection fsm_4bit_sequence_detection_sva auto_sva_inst (
    .clk(clk),
    .in(in),
    .match(match),
    .state(state),
    .MATCH(match)
);
