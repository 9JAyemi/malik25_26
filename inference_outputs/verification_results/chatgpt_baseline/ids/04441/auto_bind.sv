// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): count, estado_atual, IDLE, b0, PRESS, b1, PRESS_COUNT_THRESH, check_reset_forces_idle, assert, property, posedge, check_idle_holds_without_infrared, disable, iff, check_idle_to_press_on_infrared, check_press_holds_below_threshold, check_press_holds_at_threshold_with_infrared_low, check_press_returns_idle_at_threshold_with_infrared_high, check_count_clears_in_idle, check_count_increments_in_press, past, check_led_samples_infrared, check_buttons_always_low
bind infrared_control infrared_control_sva auto_sva_inst (
    .infrared(infrared),
    .clk(clk),
    .reset(reset),
    .led(led),
    .botao_1(botao_1),
    .botao_2(botao_2),
    .botao_3(botao_3),
    .botao_4(botao_4)
);
