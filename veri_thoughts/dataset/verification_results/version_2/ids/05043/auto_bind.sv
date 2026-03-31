// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): state, S0, b00, S1, b01, S2, b10, S3, b11, check_reset_state_and_match, assert, property, posedge, b0, check_s0_data0_stays_s0, disable, iff, check_s0_data1_to_s1, b1, check_s1_data0_to_s0, check_s1_data1_to_s2, check_s2_data0_to_s0, check_s2_data1_to_s3, check_s3_data0_stays_s3, check_s3_data1_to_s0, check_match_high_in_s3, check_match_low_outside_s3
bind fsm_consecutive_ones_counter fsm_consecutive_ones_counter_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .data(data),
    .match(match)
);
