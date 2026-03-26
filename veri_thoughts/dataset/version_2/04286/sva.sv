module binary_counter_sva(
    input logic       clk,
    input logic       reset,
    input logic       enable,
    input logic [3:0] count
);

    // Reset clears the counter on the next sampled cycle.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 4'b0000)
    );

    // Reset has priority over enable when both are asserted.
    check_reset_priority_over_enable: assert property (
        @(posedge clk) (reset && enable) |=> (count == 4'b0000)
    );

    // When enabled below the maximum value, the counter increments by one.
    check_increment_when_enabled: assert property (
        @(posedge clk) disable iff (reset)
        (enable && (count != 4'hF)) |=> (count == ($past(count) + 4'd1))
    );

    // When enabled at the maximum value, the counter wraps to zero.
    check_wrap_when_enabled_at_max: assert property (
        @(posedge clk) disable iff (reset)
        (enable && (count == 4'hF)) |=> (count == 4'h0)
    );

    // When not enabled and not in reset, the counter holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        (!enable) |=> (count == $past(count))
    );

endmodule