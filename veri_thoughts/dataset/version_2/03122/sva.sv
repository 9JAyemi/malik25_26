module counter_sva (
    input logic       clk,
    input logic       reset,
    input logic       enable,
    input logic [3:0] count
);

    // Clock: clk; reset: active-high synchronous reset.
    // Function: 4-bit counter that increments when enabled and wraps from 10 to 0.

    // Reset clears the counter to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 4'b0000)
    );

    // When disabled, the counter holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        (!enable) |=> (count == $past(count))
    );

    // When enabled and not at 10, the counter increments by one.
    check_increment_when_enabled: assert property (
        @(posedge clk) disable iff (reset)
        (enable && (count != 4'b1010)) |=> (count == ($past(count) + 4'b0001))
    );

    // When enabled at 10, the counter wraps to zero.
    check_wrap_at_ten: assert property (
        @(posedge clk) disable iff (reset)
        (enable && (count == 4'b1010)) |=> (count == 4'b0000)
    );

endmodule