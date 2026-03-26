module traffic_light_controller_sva (
    input logic reset,
    input logic clk,
    input logic green,
    input logic yellow,
    input logic red,
    input logic [1:0] state,
    input logic [5:0] counter
);

    localparam logic [1:0] GREEN_STATE  = 2'b00;
    localparam logic [1:0] YELLOW_STATE = 2'b01;
    localparam logic [1:0] RED_STATE    = 2'b10;

    // Reset returns the FSM to green with a zero counter.
    check_reset_state: assert property (
        @(posedge clk) reset |=> (state == GREEN_STATE) && (counter == 6'd0)
    );

    // Reset leads to the green output pattern.
    check_reset_outputs: assert property (
        @(posedge clk) reset |=> (green == 1'b1) && (yellow == 1'b0) && (red == 1'b0)
    );

    // Green state increments the counter before the transition point.
    check_green_count_increment: assert property (
        @(posedge clk) disable iff (reset)
        (state == GREEN_STATE && counter < 6'd30) |=> (state == GREEN_STATE) && (counter == ($past(counter) + 6'd1))
    );

    // Green state transitions to yellow when the counter reaches 30.
    check_green_to_yellow_transition: assert property (
        @(posedge clk) disable iff (reset)
        (state == GREEN_STATE && counter == 6'd30) |=> (state == YELLOW_STATE) && (counter == 6'd0)
    );

    // Yellow state increments the counter before the transition point.
    check_yellow_count_increment: assert property (
        @(posedge clk) disable iff (reset)
        (state == YELLOW_STATE && counter < 6'd5) |=> (state == YELLOW_STATE) && (counter == ($past(counter) + 6'd1))
    );

    // Yellow state transitions to red when the counter reaches 5.
    check_yellow_to_red_transition: assert property (
        @(posedge clk) disable iff (reset)
        (state == YELLOW_STATE && counter == 6'd5) |=> (state == RED_STATE) && (counter == 6'd0)
    );

    // Red state increments the counter before the transition point.
    check_red_count_increment: assert property (
        @(posedge clk) disable iff (reset)
        (state == RED_STATE && counter < 6'd25) |=> (state == RED_STATE) && (counter == ($past(counter) + 6'd1))
    );

    // Red state transitions to green when the counter reaches 25.
    check_red_to_green_transition: assert property (
        @(posedge clk) disable iff (reset)
        (state == RED_STATE && counter == 6'd25) |=> (state == GREEN_STATE) && (counter == 6'd0)
    );

    // Green state drives only green high.
    check_green_outputs: assert property (
        @(posedge clk) disable iff (reset)
        (state == GREEN_STATE) |-> (green == 1'b1) && (yellow == 1'b0) && (red == 1'b0)
    );

    // Yellow state drives only yellow high.
    check_yellow_outputs: assert property (
        @(posedge clk) disable iff (reset)
        (state == YELLOW_STATE) |-> (green == 1'b0) && (yellow == 1'b1) && (red == 1'b0)
    );

    // Red state drives only red high.
    check_red_outputs: assert property (
        @(posedge clk) disable iff (reset)
        (state == RED_STATE) |-> (green == 1'b0) && (yellow == 1'b0) && (red == 1'b1)
    );

endmodule