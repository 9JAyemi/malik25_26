// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): IDLE, PRESS, BOT14, BOT23, KEEP1, KEEP2, KEEP3, KEEP4, T_IGNOR, T_PRESS, led_on_when_infrared, assert, property, posedge, disable, iff, b1, led_off_when_infrared, b0, state_transition_idle_to_press, estado_atual, estado_prox, state_transition_press_to_bot14, count, state_transition_press_to_bot23, state_transition_bot14_to_keep4, state_transition_bot14_to_keep1, state_transition_bot23_to_keep3, state_transition_bot23_to_keep2, state_transition_keep1_to_idle, state_transition_keep2_to_idle, state_transition_keep3_to_idle, state_transition_keep4_to_idle, botao_1_on_when_bot14_and_infrared, botao_1_off_when_bot14_and_not_infrared, botao_2_on_when_bot23_and_infrared, botao_2_off_when_bot23_and_not_infrared, botao_3_on_when_keep1_and_count, botao_3_off_when_keep1_and_count, botao_4_on_when_keep2_and_count, botao_4_off_when_keep2_and_count, botao_3_on_when_keep3_and_count, botao_3_off_when_keep3_and_count
bind infrared_control infrared_control_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .infrared(infrared),
    .led(led),
    .botao_1(botao_1),
    .botao_2(botao_2),
    .botao_3(botao_3),
    .botao_4(botao_4)
);
