// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): state, green_counter, yellow_counter, red_counter, GREEN, b00, YELLOW, b01, RED, b10, reset_state_counters, assert, property, posedge, d0, reset_outputs_green, b1, b0, state_valid_encoding, disable, iff, decode_green, decode_yellow, decode_red, leds_onehot, onehot, green_count_increments, past, d10, green_to_yellow_on_10, green_counter_bounded, yellow_count_increments, d2, yellow_to_red_on_2, yellow_counter_bounded, red_count_increments, d15, red_to_green_on_15, red_counter_bounded, green_zero_outside_green, yellow_zero_outside_yellow, red_zero_outside_red
bind traffic_light_controller traffic_light_controller_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .green_led(green_led),
    .yellow_led(yellow_led),
    .red_led(red_led)
);
