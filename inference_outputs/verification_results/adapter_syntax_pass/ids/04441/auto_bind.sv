// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): estado_atual, estado_prox, count, IDLE, d0, PRESS, d1, BOT14, d2, BOT23, d3, KEEP1, d4, KEEP2, d5, KEEP3, d6, KEEP4, d7, T_IGNOR, T_PRESS, check_led_matches_infrared, assert, property, posedge, disable, iff, check_count_increments_in_active_states, inside, past, check_count_resets_in_inactive_states, check_idle_holds_without_infrared, b0, check_idle_advances_to_press, b1, check_press_holds_until_timeout, check_press_advances_to_bot14, check_press_advances_to_bot23, check_bot14_holds_until_timeout, check_bot14_advances_to_keep4, check_bot14_advances_to_keep1, check_bot23_holds_until_timeout, check_bot23_advances_to_keep3, check_bot23_advances_to_keep2, check_keep1_holds_until_timeout, check_keep1_returns_to_idle, check_keep2_holds_until_timeout, check_keep2_returns_to_idle, check_keep3_holds_until_timeout, check_keep3_returns_to_idle, check_keep4_holds_until_timeout, check_keep4_returns_to_idle, check_botao_1_active_states, check_botao_2_active_states, check_botao_3_active_states, check_botao_4_active_states, check_botao_12_mutex
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
