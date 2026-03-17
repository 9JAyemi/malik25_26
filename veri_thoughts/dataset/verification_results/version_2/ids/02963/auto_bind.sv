// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): state, next_state, S0, b00, S1, b01, S2, b10, S3, b11, reset_forces_S0, assert, property, posedge, state_updates_from_next_nonreset, disable, iff, past, outputs_decode_S0, b1, b0, outputs_decode_S1, outputs_decode_S2, outputs_decode_S3, check_lights_mutex, comb_next_S0_no_ped, comb_next_S0_with_ped, comb_next_S1_to_S2, comb_next_S2_to_S3, comb_next_S3_to_S0, trans_S0_ped0_stay, trans_S0_ped1_to_S1, trans_S1_to_S2, trans_S2_to_S3, trans_S3_to_S0
bind fsm_traffic_light_control fsm_traffic_light_control_sva auto_sva_inst (
    .clock(clock),
    .reset(reset),
    .pedestrian_crossing_button(pedestrian_crossing_button),
    .green_light(green_light),
    .yellow_light(yellow_light),
    .red_light(red_light)
);
