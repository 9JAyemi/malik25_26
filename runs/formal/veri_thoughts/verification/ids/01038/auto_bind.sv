// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): current_state, previous_state, debounce_counter, check_counter_increments_until_limit, assert, property, posedge, d10000, past, d1, check_counter_saturates_at_limit, check_counter_never_exceeds_limit, check_current_state_samples_button, b1, check_previous_state_tracks_current, check_button_state_stable_before_limit, stable, check_button_state_follows_current_at_limit, check_button_down_rise_requires_event, rose, check_button_up_rise_requires_event, check_button_down_set_on_down_event, check_button_up_set_on_up_event, check_button_pulse_rise_mutex, check_button_down_never_falls, fell, check_button_up_never_falls
bind debounce debounce_sva auto_sva_inst (
    .clk(clk),
    .button(button),
    .button_state(button_state),
    .button_up(button_up),
    .button_down(button_down)
);
