// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_led_follows_infrared, assert, property, posedge, disable, iff, past, check_botao_1_decode, b1, KEEP1, count, T_PRESS, check_botao_2_decode, KEEP2, check_botao_3_decode, KEEP3, check_botao_4_decode, KEEP4, check_botao_12_mutex, check_botao_13_mutex, check_botao_14_mutex, check_botao_23_mutex, check_botao_24_mutex, check_botao_34_mutex, check_botao_1_one_cycle, check_botao_2_one_cycle, check_botao_3_one_cycle, check_botao_4_one_cycle
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
