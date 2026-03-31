module counter_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [3:0] count,
    input logic overflow
);

    // Reset clears the counter and deasserts overflow.
    check_reset_clears_state: assert property (
        @(posedge clk) reset |=> (count == 4'h0 && overflow == 1'b0)
    );

    // When enabled below 15, the counter increments by one.
    check_count_increments_when_enabled: assert property (
        @(posedge clk) disable iff (reset)
        enable && (count != 4'hF) |=> (count == ($past(count) + 4'd1))
    );

    // When enabled at 15, the counter wraps to zero.
    check_count_wraps_at_max: assert property (
        @(posedge clk) disable iff (reset)
        enable && (count == 4'hF) |=> (count == 4'h0)
    );

    // When enabled below 15, overflow remains low.
    check_overflow_low_when_incrementing: assert property (
        @(posedge clk) disable iff (reset)
        enable && (count != 4'hF) |=> (overflow == 1'b0)
    );

    // When enabled at 15, overflow is asserted on the next cycle.
    check_overflow_asserts_at_max: assert property (
        @(posedge clk) disable iff (reset)
        enable && (count == 4'hF) |=> (overflow == 1'b1)
    );

    // When not enabled, the counter holds its value.
    check_count_holds_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        !enable |=> (count == $past(count))
    );

    // When not enabled, overflow holds its value.
    check_overflow_holds_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        !enable |=> (overflow == $past(overflow))
    );

endmodule