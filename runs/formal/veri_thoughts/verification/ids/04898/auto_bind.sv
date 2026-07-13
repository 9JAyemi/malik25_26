// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): key_state, next_key_state, KEY_FREE, b00, KEY_PRESSED, b01, KEY_RELEASED, b10, check_reset_state, assert, property, posedge, check_reset_output, b0, check_next_free_to_pressed, disable, iff, check_next_free_stays_free, b1, check_next_pressed_stays_pressed, check_next_pressed_to_released, check_next_released_to_free, check_state_free_to_pressed, check_state_free_stays_free, check_state_pressed_stays_pressed, check_state_pressed_to_released, check_state_released_to_free, check_output_low_in_free, check_output_low_in_pressed, check_output_high_in_released
bind keypressed keypressed_sva auto_sva_inst (
    .clock(clock),
    .reset(reset),
    .enable_in(enable_in),
    .enable_out(enable_out)
);
