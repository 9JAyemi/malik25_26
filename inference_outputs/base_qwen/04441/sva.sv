```systemverilog
module infrared_control_sva (
    input logic clk,
    input logic reset,
    input logic infrared,
    output logic led,
    output logic botao_1,
    output logic botao_2,
    output logic botao_3,
    output logic botao_4
);
    parameter IDLE  = 0; parameter PRESS = 1; parameter BOT14 = 2; parameter BOT23 = 3; parameter KEEP1 = 4; parameter KEEP2 = 5; parameter KEEP3 = 6; parameter KEEP4 = 7; parameter T_IGNOR = 57000; parameter T_PRESS = 950;

    // LED should be ON when infrared is ON
    led_on_when_infrared: assert property (
        @(posedge clk) disable iff (!reset) (infrared == 1'b1) |-> (led == 1'b1)
    );

    // LED should be OFF when infrared is OFF
    led_off_when_infrared: assert property (
        @(posedge clk) disable iff (!reset) (infrared == 1'b0) |-> (led == 1'b0)
    );

    // State transition from IDLE to PRESS when infrared is ON
    state_transition_idle_to_press: assert property (
        @(posedge clk) disable iff (!reset) (infrared == 1'b1) |-> (estado_atual == IDLE) |-> (estado_prox == PRESS)
    );

    // State transition from PRESS to BOT14 when count >= 130 and infrared is ON
    state_transition_press_to_bot14: assert property (
        @(posedge clk) disable iff (!reset) (count >= 130) |-> (infrared == 1'b1) |-> (estado_atual == PRESS) |-> (estado_prox == BOT14)
    );

    // State transition from PRESS to BOT23 when count >= 130 and infrared is OFF
    state_transition_press_to_bot23: assert property (
        @(posedge clk) disable iff (!reset) (count >= 130) |-> (infrared == 1'b0) |-> (estado_atual == PRESS) |-> (estado_prox == BOT23)
    );

    // State transition from BOT14 to KEEP4 when count >= 190 and infrared is ON
    state_transition_bot14_to_keep4: assert property (
        @(posedge clk) disable iff (!reset) (count >= 190) |-> (infrared == 1'b1) |-> (estado_atual == BOT14) |-> (estado_prox == KEEP4)
    );

    // State transition from BOT14 to KEEP1 when count >= 190 and infrared is OFF
    state_transition_bot14_to_keep1: assert property (
        @(posedge clk) disable iff (!reset) (count >= 190) |-> (infrared == 1'b0) |-> (estado_atual == BOT14) |-> (estado_prox == KEEP1)
    );

    // State transition from BOT23 to KEEP3 when count >= 170 and infrared is ON
    state_transition_bot23_to_keep3: assert property (
        @(posedge clk) disable iff (!reset) (count >= 170) |-> (infrared == 1'b1) |-> (estado_atual == BOT23) |-> (estado_prox == KEEP3)
    );

    // State transition from BOT23 to KEEP2 when count >= 170 and infrared is OFF
    state_transition_bot23_to_keep2: assert property (
        @(posedge clk) disable iff (!reset) (count >= 170) |-> (infrared == 1'b0) |-> (estado_atual == BOT23) |-> (estado_prox == KEEP2)
    );

    // State transition from KEEP1 to IDLE when count >= T_IGNOR
    state_transition_keep1_to_idle: assert property (
        @(posedge clk) disable iff (!reset) (count >= T_IGNOR) |-> (estado_atual == KEEP1) |-> (estado_prox == IDLE)
    );

    // State transition from KEEP2 to IDLE when count >= T_IGNOR
    state_transition_keep2_to_idle: assert property (
        @(posedge clk) disable iff (!reset) (count >= T_IGNOR) |-> (estado_atual == KEEP2) |-> (estado_prox == IDLE)
    );

    // State transition from KEEP3 to IDLE when count >= T_IGNOR
    state_transition_keep3_to_idle: assert property (
        @(posedge clk) disable iff (!reset) (count >= T_IGNOR) |-> (estado_atual == KEEP3) |-> (estado_prox == IDLE)
    );

    // State transition from KEEP4 to IDLE when count >= T_IGNOR
    state_transition_keep4_to_idle: assert property (
        @(posedge clk) disable iff (!reset) (count >= T_IGNOR) |-> (estado_atual == KEEP4) |-> (estado_prox == IDLE)
    );

    // Botao_1 should be ON when estado_atual is BOT14 and count >= 190 and infrared is ON
    botao_1_on_when_bot14_and_infrared: assert property (
        @(posedge clk) disable iff (!reset) (estado_atual == BOT14) |-> (count >= 190) |-> (infrared == 1'b1) |-> (botao_1 == 1'b1)
    );

    // Botao_1 should be OFF when estado_atual is BOT14 and count >= 190 and infrared is OFF
    botao_1_off_when_bot14_and_not_infrared: assert property (
        @(posedge clk) disable iff (!reset) (estado_atual == BOT14) |-> (count >= 190) |-> (infrared == 1'b0) |-> (botao_1 == 1'b0)
    );

    // Botao_2 should be ON when estado_atual is BOT23 and count >= 170 and infrared is ON
    botao_2_on_when_bot23_and_infrared: assert property (
        @(posedge clk) disable iff (!reset) (estado_atual == BOT23) |-> (count >= 170) |-> (infrared == 1'b1) |-> (botao_2 == 1'b1)
    );

    // Botao_2 should be OFF when estado_atual is BOT23 and count >= 170 and infrared is OFF
    botao_2_off_when_bot23_and_not_infrared: assert property (
        @(posedge clk) disable iff (!reset) (estado_atual == BOT23) |-> (count >= 170) |-> (infrared == 1'b0) |-> (botao_2 == 1'b0)
    );

    // Botao_3 should be ON when estado_atual is KEEP1 and count >= T_PRESS
    botao_3_on_when_keep1_and_count: assert property (
        @(posedge clk) disable iff (!reset) (estado_atual == KEEP1) |-> (count >= T_PRESS) |-> (botao_3 == 1'b1)
    );

    // Botao_3 should be OFF when estado_atual is KEEP1 and count < T_PRESS
    botao_3_off_when_keep1_and_count: assert property (
        @(posedge clk) disable iff (!reset) (estado_atual == KEEP1) |-> (count < T_PRESS) |-> (botao_3 == 1'b0)
    );

    // Botao_4 should be ON when estado_atual is KEEP2 and count >= T_PRESS
    botao_4_on_when_keep2_and_count: assert property (
        @(posedge clk) disable iff (!reset) (estado_atual == KEEP2) |-> (count >= T_PRESS) |-> (botao_4 == 1'b1)
    );

    // Botao_4 should be OFF when estado_atual is KEEP2 and count < T_PRESS
    botao_4_off_when_keep2_and_count: assert property (
        @(posedge clk) disable iff (!reset) (estado_atual == KEEP2) |-> (count < T_PRESS) |-> (botao_4 == 1'b0)
    );

    // Botao_3 should be ON when estado_atual is KEEP3 and count >= T_PRESS
    botao_3_on_when_keep3_and_count: assert property (
        @(posedge clk) disable iff (!reset) (estado_atual == KEEP3) |-> (count >= T_PRESS) |-> (botao_3 == 1'b1)
    );

    // Botao_3 should be OFF when estado_atual is KEEP3 and count < T_PRESS
    botao_3_off_when_keep3_and_count: assert property (
        @(posedge clk) disable iff (!reset) (estado_atual == KEEP3) |-> (count < T_PRESS) |-> (botao_3 == 1'b0)
    );

    // Botao_4 should be ON when estado_atual is KEEP4 and count >= T_PRESS
    botao_4_on_when_keep4_and_count: assert property (
        @(posedge clk) disable iff (!reset) (estado_atual == KEEP4) |-> (count >= T_PRESS) |-> (botao_4 == 