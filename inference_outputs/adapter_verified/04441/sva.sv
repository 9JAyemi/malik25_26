module infrared_control_sva (
    input logic infrared,
    input logic clk,
    input logic reset,
    input logic led,
    input logic botao_1,
    input logic botao_2,
    input logic botao_3,
    input logic botao_4
);

// Clock: clk; Reset: reset (active-high, synchronous). Logic is mixed: sequential state machine with combinational outputs.

    // LED is high when infrared is high.
    check_led_high_when_infrared_high: assert property (
        @(posedge clk) disable iff (reset) (infrared == 1'b1) |-> (led == 1'b1)
    );

// LED is low when infrared is low.
    check_led_low_when_infrared_low: assert property (
        @(posedge clk) disable iff (reset) (infrared == 1'b0) |-> (led == 1'b0)
    );

// Botão 1 is high only in KEEP1 with count >= T_PRESS.
    check_botao_1_only_in_keep1: assert property (
        @(posedge clk) disable iff (reset) (estado_atual == KEEP1 && count >= T_PRESS) |-> (botao_1 == 1'b1 && botao_2 == 1'b0 && botao_3 == 1'b0 && botao_4 == 1'b0)
    );

// Botão 2 is high only in KEEP2 with count >= T_PRESS.
    check_botao_2_only_in_keep2: assert property (
        @(posedge clk) disable iff (reset) (estado_atual == KEEP2 && count >= T_PRESS) |-> (botao_1 == 1'b0 && botao_2 == 1'b1 && botao_3 == 1'b0 && botao_4 == 1'b0)
    );

// Botão 3 is high only in KEEP3 with count >= T_PRESS.
    check_botao_3_only_in_keep3: assert property (
        @(posedge clk) disable iff (reset) (estado_atual == KEEP3 && count >= T_PRESS) |-> (botao_1 == 1'b0 && botao_2 == 1'b0 && botao_3 == 1'b1 && botao_4 == 1'b0)
    );

// Botão 4 is high only in KEEP4 with count >= T_PRESS.
    check_botao_4_only_in_keep4: assert property (
        @(posedge clk) disable iff (reset) (estado_atual == KEEP4 && count >= T_PRESS) |-> (botao_1 == 1'b0 && botao_2 == 1'b0 && botao_3 == 1'b0 && botao_4 == 1'b1)
    );

// Botão 1 is low everywhere except KEEP1 with count >= T_PRESS.
    check_botao_1_low_elsewhere: assert property (
        @(posedge clk) disable iff (reset) (!((estado_atual == KEEP1) && (count >= T_PRESS))) |-> (botao_1 == 1'b0)
    );

// Botão 2 is low everywhere except KEEP2 with count >= T_PRESS.
    check_botao_2_low_elsewhere: assert property (
        @(posedge clk) disable iff (reset) (!((estado_atual == KEEP2) && (count >= T_PRESS))) |-> (botao_2 == 1'b0)
    );

// Botão 3 is low everywhere except KEEP3 with count >= T_PRESS.
    check_botao_3_low_elsewhere: assert property (
        @(posedge clk) disable iff (reset) (!((estado_atual == KEEP3) && (count >= T_PRESS))) |-> (botao_3 == 1'b0)
    );

// Botão 4 is low everywhere except KEEP4 with count >= T_PRESS.
    check_botao_4_low_elsewhere: assert property (
        @(posedge clk) disable iff (reset) (!((estado_atual == KEEP4) && (count >= T_PRESS))) |-> (botao_4 == 1'b0)
    );

endmodule
