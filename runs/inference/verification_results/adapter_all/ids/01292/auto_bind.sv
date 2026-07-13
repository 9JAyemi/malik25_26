// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_next_state_decode, assert, property, b1, past, check_state_updates_from_next_state, check_out_matches_state, check_state0_low_stays, check_state0_high_to_state1, check_state1_low_to_state0, check_state1_high_to_state2, check_state2_low_to_state0, check_state2_high_stays, check_out_changes_only_from_state2, changed
bind seq_detector seq_detector_sva auto_sva_inst (
    .in(in),
    .out(out),
    .clk(clk),
    .state(state),
    .next_state(next_state),
    .state0(state0),
    .b00(b00),
    .state1(state1),
    .b01(b01),
    .state2(state2),
    .b10(b10),
    .posedge(posedge),
    .b0(b0)
);
