module counter_4bit_assertions (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [3:0] Q
);

    // Clock: clk
    // Reset: reset, active high asynchronous

    // A sampled reset must leave the counter at zero by the next clock.
    check_reset_clears_q: assert property (
        @(posedge clk) reset |=> (Q == 4'b0000)
    );

    // When disabled outside reset, the counter holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        !enable |=> (Q == $past(Q))
    );

    // When enabled below 15, the counter increments by one.
    check_increment_when_enabled: assert property (
        @(posedge clk) disable iff (reset)
        enable && (Q != 4'hF) |=> (Q == ($past(Q) + 4'd1))
    );

    // When enabled at 15, the counter wraps to zero.
    check_wrap_when_enabled_at_max: assert property (
        @(posedge clk) disable iff (reset)
        enable && (Q == 4'hF) |=> (Q == 4'h0)
    );

endmodule