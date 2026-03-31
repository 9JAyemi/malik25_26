module counter_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [3:0] count,
    input logic overflow
);

// Reset clears both count and overflow on the next cycle.
    check_reset_clears_outputs: assert property (
        @(posedge clk) reset |=> (count == 4'h0) && (overflow == 1'b0)
    );

// When enabled below max, count increments by one.
    check_count_increments: assert property (
        @(posedge clk) disable iff (reset)
        (enable && (count != 4'hF)) |=> (count == ($past(count) + 4'd1))
    );

// When enabled at max, count wraps to zero.
    check_count_wraps: assert property (
        @(posedge clk) disable iff (reset)
        (enable && (count == 4'hF)) |=> (count == 4'h0)
    );

// When enabled below max, overflow is cleared.
    check_overflow_clears: assert property (
        @(posedge clk) disable iff (reset)
        (enable && (count != 4'hF)) |=> (overflow == 1'b0)
    );

// When enabled at max, overflow is asserted.
    check_overflow_asserts: assert property (
        @(posedge clk) disable iff (reset)
        (enable && (count == 4'hF)) |=> (overflow == 1'b1)
    );

// When not enabled, count holds its value.
    check_count_holds_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        (!enable) |=> (count == $past(count))
    );

// When not enabled, overflow holds its value.
    check_overflow_holds_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        (!enable) |=> (overflow == $past(overflow))
    );

endmodule
