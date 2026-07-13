// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): clk, check_green_with_ped_to_yellow, assert, property, posedge, b00, b01, check_green_without_ped_to_red, b10, check_yellow_to_red, check_red_to_green, check_default_to_green, b11, check_next_state_never_invalid, b1, check_yellow_output_source, check_green_output_source, check_red_output_source
bind traffic_light traffic_light_sva auto_sva_inst (
    .current_state(current_state),
    .pedestrian_button(pedestrian_button),
    .next_state(next_state)
);
