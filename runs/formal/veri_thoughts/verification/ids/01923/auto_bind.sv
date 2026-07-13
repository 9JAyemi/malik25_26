// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_forces_zeros, assert, property, global_clock, b0, red_mapping_when_not_reset, disable, iff, green_mapping_when_not_reset, concat_mapping_when_not_reset, stable_inputs_imply_stable_outputs, stable, low_half_change_affects_only_red, changed, high_half_change_affects_only_green, any_input_change_changes_outputs, red_change_implies_low_input_change, green_change_implies_high_input_change
bind switch_to_leds switch_to_leds_sva auto_sva_inst (
    .switch_input(switch_input),
    .reset(reset),
    .red_led_output(red_led_output),
    .green_led_output(green_led_output)
);
