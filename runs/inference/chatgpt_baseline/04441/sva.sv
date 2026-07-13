module infrared_control_sva (
    input logic infrared,
    input logic clk,
    input logic reset,
    input logic led,
    input logic botao_1,
    input logic botao_2,
    input logic botao_3,
    input logic botao_4,
    input integer count,
    input logic estado_atual
);

    localparam logic IDLE  = 1'b0;
    localparam logic PRESS = 1'b1;
    localparam integer PRESS_COUNT_THRESH = 130;

    // Synchronous reset drives the state to IDLE.
    check_reset_forces_idle: assert property (
        @(posedge clk) reset |=> (estado_atual == IDLE)
    );

    // IDLE holds when infrared is low.
    check_idle_holds_without_infrared: assert property (
        @(posedge clk) disable iff (reset)
        (estado_atual == IDLE && infrared == 1'b0) |=> (estado_atual == IDLE)
    );

    // IDLE enters PRESS when infrared is high.
    check_idle_to_press_on_infrared: assert property (
        @(posedge clk) disable iff (reset)
        (estado_atual == IDLE && infrared == 1'b1) |=> (estado_atual == PRESS)
    );

    // PRESS holds while count is below 130.
    check_press_holds_below_threshold: assert property (
        @(posedge clk) disable iff (reset)
        (estado_atual == PRESS && count < PRESS_COUNT_THRESH) |=> (estado_atual == PRESS)
    );

    // PRESS holds when count is at least 130 and infrared is low.
    check_press_holds_at_threshold_with_infrared_low: assert property (
        @(posedge clk) disable iff (reset)
        (estado_atual == PRESS && count >= PRESS_COUNT_THRESH && infrared == 1'b0) |=> (estado_atual == PRESS)
    );

    // PRESS returns to IDLE when count is at least 130 and infrared is high.
    check_press_returns_idle_at_threshold_with_infrared_high: assert property (
        @(posedge clk) disable iff (reset)
        (estado_atual == PRESS && count >= PRESS_COUNT_THRESH && infrared == 1'b1) |=> (estado_atual == IDLE)
    );

    // IDLE clears the counter on the next cycle.
    check_count_clears_in_idle: assert property (
        @(posedge clk) disable iff (reset)
        (estado_atual == IDLE) |=> (count == 0)
    );

    // PRESS increments the counter on the next cycle.
    check_count_increments_in_press: assert property (
        @(posedge clk) disable iff (reset)
        (estado_atual == PRESS) |=> (count == $past(count) + 1)
    );

    // LED captures the previous cycle's infrared sample.
    check_led_samples_infrared: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (led == $past(infrared))
    );

    // Button outputs are never asserted.
    check_buttons_always_low: assert property (
        @(posedge clk) disable iff (reset)
        (botao_1 == 1'b0 && botao_2 == 1'b0 && botao_3 == 1'b0 && botao_4 == 1'b0)
    );

endmodule