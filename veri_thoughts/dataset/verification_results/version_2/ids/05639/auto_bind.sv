// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): state, counter, GREEN_STATE, b00, YELLOW_STATE, b01, RED_STATE, b10, check_reset_state, assert, property, posedge, d0, check_reset_outputs, b1, b0, check_green_count_increment, disable, iff, d30, past, d1, check_green_to_yellow_transition, check_yellow_count_increment, d5, check_yellow_to_red_transition, check_red_count_increment, d25, check_red_to_green_transition, check_green_outputs, check_yellow_outputs, check_red_outputs
bind traffic_light_controller traffic_light_controller_sva auto_sva_inst (
    .reset(reset),
    .clk(clk),
    .green(green),
    .yellow(yellow),
    .red(red)
);
