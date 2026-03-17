// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_clears_reg, assert, property, posedge, b0000, load_on_enable, disable, iff, past, hold_when_enable_stays_low, led_fail_is_invert_success, led_success_matches_compare, leds_match_zero_during_reset, leds_one_hot, led_success_updates_after_enable, leds_stable_when_inputs_stable, stable
bind Comparador Comparador_sva auto_sva_inst (
    .clock(clock),
    .reset(reset),
    .write_value(write_value),
    .read_value(read_value),
    .read_value_reg_en(read_value_reg_en),
    .led_success(led_success),
    .led_fail(led_fail),
    .read_value_reg(read_value_reg)
);
