// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_led_high_when_infrared_high, assert, property, posedge, disable, iff, b1, check_led_low_when_infrared_low, b0, check_botao_1_only_in_keep1, estado_atual, KEEP1, count, T_PRESS, check_botao_2_only_in_keep2, KEEP2, check_botao_3_only_in_keep3, KEEP3, check_botao_4_only_in_keep4, KEEP4, check_botao_1_low_elsewhere, check_botao_2_low_elsewhere, check_botao_3_low_elsewhere, check_botao_4_low_elsewhere
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
