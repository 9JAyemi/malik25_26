// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_state_and_match, assert, property, check_s0_next_state_decoding, disable, iff, b001, check_s1_next_state_decoding, b010, check_s2_next_state_decoding, b100, check_s3_next_state_decoding, check_state_register_update, b1, past, check_match_register_update, check_s3_returns_to_s0_with_match, check_mismatch_returns_to_s0, check_full_pattern_detection
bind fsm_3bit_pattern_detection fsm_3bit_pattern_detection_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .data(data),
    .match(match),
    .state(state),
    .next_state(next_state),
    .S0(S0),
    .b00(b00),
    .S1(S1),
    .b01(b01),
    .S2(S2),
    .b10(b10),
    .S3(S3),
    .b11(b11),
    .posedge(posedge),
    .b0(b0)
);
