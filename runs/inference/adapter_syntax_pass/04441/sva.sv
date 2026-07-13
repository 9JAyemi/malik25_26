module infrared_control_sva (
    input logic infrared,
    input logic clk,
    input logic reset,
    input logic led,
    input logic botao_1,
    input logic botao_2,
    input logic botao_3,
    input logic botao_4,
    input logic estado_atual,
    input logic estado_prox,
    input integer count
);

    localparam logic [2:0] IDLE  = 3'd0;
    localparam logic [2:0] PRESS = 3'd1;
    localparam logic [2:0] BOT14 = 3'd2;
    localparam logic [2:0] BOT23 = 3'd3;
    localparam logic [2:0] KEEP1 = 3'd4;
    localparam logic [2:0] KEEP2 = 3'd5;
    localparam logic [2:0] KEEP3 = 3'd6;
    localparam logic [2:0] KEEP4 = 3'd7;

    localparam integer T_IGNOR = 57000;
    localparam integer T_PRESS = 950;

    // LED is driven directly from infrared.
    check_led_matches_infrared: assert property (
        @(posedge clk) disable iff (reset)
        led == infrared
    );

    // count increments by one in all active states.
    check_count_increments_in_active_states: assert property (
        @(posedge clk) disable iff (reset)
        (estado_atual inside {PRESS, BOT14, BOT23, KEEP1, KEEP2, KEEP3, KEEP4}) |-> (count == ($past(count) + 1))
    );

    // count resets to zero in all non-active states.
    check_count_resets_in_inactive_states: assert property (
        @(posedge clk) disable iff (reset)
        !(estado_atual inside {PRESS, BOT14, BOT23, KEEP1, KEEP2, KEEP3, KEEP4}) |-> (count == 0)
    );

    // IDLE holds when no infrared pulse is detected.
    check_idle_holds_without_infrared: assert property (
        @(posedge clk) disable iff (reset)
        (estado_atual == IDLE) && (infrared == 1'b0) |-> (estado_prox == IDLE)
    );

    // IDLE advances to PRESS when infrared is detected.
    check_idle_advances_to_press: assert property (
        @(posedge clk) disable iff (reset)
        (estado_atual == IDLE) && (infrared == 1'b1) |-> (estado_prox == PRESS)
    );

    // PRESS holds until the press timeout is reached.
    check_press_holds_until_timeout: assert property (
        @(posedge clk) disable iff (reset)
        (estado_atual == PRESS) && (count < 130) |-> (estado_prox == PRESS)
    );

    // PRESS advances to BOT14 when infrared is high at timeout.
    check_press_advances_to_bot14: assert property (
        @(posedge clk) disable iff (reset)
        (estado_atual == PRESS) && (count >= 130) && (infrared == 1'b1) |-> (estado_prox == BOT14)
    );

    // PRESS advances to BOT23 when infrared is low at timeout.
    check_press_advances_to_bot23: assert property (
        @(posedge clk) disable iff (reset)
        (estado_atual == PRESS) && (count >= 130) && (infrared == 1'b0) |-> (estado_prox == BOT23)
    );

    // BOT14 holds until the hold timeout is reached.
    check_bot14_holds_until_timeout: assert property (
        @(posedge clk) disable iff (reset)
        (estado_atual == BOT14) && (count < 190) |-> (estado_prox == BOT14)
    );

    // BOT14 advances to KEEP4 when infrared is high at timeout.
    check_bot14_advances_to_keep4: assert property (
        @(posedge clk) disable iff (reset)
        (estado_atual == BOT14) && (count >= 190) && (infrared == 1'b1) |-> (estado_prox == KEEP4)
    );

    // BOT14 advances to KEEP1 when infrared is low at timeout.
    check_bot14_advances_to_keep1: assert property (
        @(posedge clk) disable iff (reset)
        (estado_atual == BOT14) && (count >= 190) && (infrared == 1'b0) |-> (estado_prox == KEEP1)
    );

    // BOT23 holds until the hold timeout is reached.
    check_bot23_holds_until_timeout: assert property (
        @(posedge clk) disable iff (reset)
        (estado_atual == BOT23) && (count < 170) |-> (estado_prox == BOT23)
    );

    // BOT23 advances to KEEP3 when infrared is high at timeout.
    check_bot23_advances_to_keep3: assert property (
        @(posedge clk) disable iff (reset)
        (estado_atual == BOT23) && (count >= 170) && (infrared == 1'b1) |-> (estado_prox == KEEP3)
    );

    // BOT23 advances to KEEP2 when infrared is low at timeout.
    check_bot23_advances_to_keep2: assert property (
        @(posedge clk) disable iff (reset)
        (estado_atual == BOT23) && (count >= 170) && (infrared == 1'b0) |-> (estado_prox == KEEP2)
    );

    // KEEP1 holds until the keep timeout is reached.
    check_keep1_holds_until_timeout: assert property (
        @(posedge clk) disable iff (reset)
        (estado_atual == KEEP1) && (count < T_IGNOR) |-> (estado_prox == KEEP1)
    );

    // KEEP1 returns to IDLE when the keep timeout is reached.
    check_keep1_returns_to_idle: assert property (
        @(posedge clk) disable iff (reset)
        (estado_atual == KEEP1) && (count >= T_IGNOR) |-> (estado_prox == IDLE)
    );

    // KEEP2 holds until the keep timeout is reached.
    check_keep2_holds_until_timeout: assert property (
        @(posedge clk) disable iff (reset)
        (estado_atual == KEEP2) && (count < T_IGNOR) |-> (estado_prox == KEEP2)
    );

    // KEEP2 returns to IDLE when the keep timeout is reached.
    check_keep2_returns_to_idle: assert property (
        @(posedge clk) disable iff (reset)
        (estado_atual == KEEP2) && (count >= T_IGNOR) |-> (estado_prox == IDLE)
    );

    // KEEP3 holds until the keep timeout is reached.
    check_keep3_holds_until_timeout: assert property (
        @(posedge clk) disable iff (reset)
        (estado_atual == KEEP3) && (count < T_IGNOR) |-> (estado_prox == KEEP3)
    );

    // KEEP3 returns to IDLE when the keep timeout is reached.
    check_keep3_returns_to_idle: assert property (
        @(posedge clk) disable iff (reset)
        (estado_atual == KEEP3) && (count >= T_IGNOR) |-> (estado_prox == IDLE)
    );

    // KEEP4 holds until the keep timeout is reached.
    check_keep4_holds_until_timeout: assert property (
        @(posedge clk) disable iff (reset)
        (estado_atual == KEEP4) && (count < T_IGNOR) |-> (estado_prox == KEEP4)
    );

    // KEEP4 returns to IDLE when the keep timeout is reached.
    check_keep4_returns_to_idle: assert property (
        @(posedge clk) disable iff (reset)
        (estado_atual == KEEP4) && (count >= T_IGNOR) |-> (estado_prox == IDLE)
    );

    // botao_1 is asserted only in KEEP1 and KEEP4.
    check_botao_1_active_states: assert property (
        @(posedge clk) disable iff (reset)
        botao_1 |-> (estado_atual inside {KEEP1, KEEP4})
    );

    // botao_2 is asserted only in KEEP2 and KEEP3.
    check_botao_2_active_states: assert property (
        @(posedge clk) disable iff (reset)
        botao_2 |-> (estado_atual inside {KEEP2, KEEP3})
    );

    // botao_3 is asserted only in KEEP3 and BOT23.
    check_botao_3_active_states: assert property (
        @(posedge clk) disable iff (reset)
        botao_3 |-> (estado_atual inside {KEEP3, BOT23})
    );

    // botao_4 is asserted only in KEEP4 and BOT14.
    check_botao_4_active_states: assert property (
        @(posedge clk) disable iff (reset)
        botao_4 |-> (estado_atual inside {KEEP4, BOT14})
    );

    // botao_1 and botao_2 are never asserted together.
    check_botao_12_mutex: assert property (
        @(posedge clk) disable iff (reset)
        !(botao_1 && botao_2)
    );

