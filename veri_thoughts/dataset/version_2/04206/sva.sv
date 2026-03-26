module counter_3bit_assertions (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [2:0] count
);

    // clk is the only clock; reset is active-high synchronous.
    // count is a 3-bit enabled up-counter with wrap from 7 to 0.

    // Reset forces the counter to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 3'd0)
    );

    // When disabled outside reset, the counter holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        (!enable) |=> $stable(count)
    );

    // When enabled below 7, the counter increments by one.
    check_increment_when_enabled_below_max: assert property (
        @(posedge clk) disable iff (reset)
        (enable && (count != 3'd7)) |=> (count == ($past(count) + 3'd1))
    );

    // When enabled at 7, the counter wraps back to zero.
    check_wrap_when_enabled_at_max: assert property (
        @(posedge clk) disable iff (reset)
        (enable && (count == 3'd7)) |=> (count == 3'd0)
    );

endmodule