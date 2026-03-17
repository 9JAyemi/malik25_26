// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): state, count_reg, S0, b00, S1, b01, check_reset_initialization, assert, property, posedge, d0, check_output_zero_in_S0, disable, iff, check_output_matches_reg_in_S1, check_S0_to_S1_on_all_ones, hFFFF, d1, check_S0_stay_on_not_all_ones, check_S1_stay_and_increment_on_all_ones, initstate, past, check_S1_to_S0_on_not_all_ones, check_stay_S1_requires_prev_all_ones, check_S0_to_S1_requires_prev_all_ones, check_S1_to_S0_requires_prev_not_all_ones
bind fsm_consecutive_ones_detection fsm_consecutive_ones_detection_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .data(data),
    .count(count)
);
