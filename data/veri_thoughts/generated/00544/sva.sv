module up_counter_sva (
    input logic       clk,
    input logic       reset,
    input logic       enable,
    input logic [2:0] count
);

    // Active-high synchronous reset clears the counter on the next cycle.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 3'b000)
    );

    // When disabled outside reset, the counter holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        (!enable) |=> (count == $past(count))
    );

    // When enabled below 7, the counter increments by one.
    check_increment_when_enabled: assert property (
        @(posedge clk) disable iff (reset)
        (enable && (count != 3'b111)) |=> (count == ($past(count) + 3'b001))
    );

    // When enabled at 7, the counter wraps back to zero.
    check_wrap_when_max: assert property (
        @(posedge clk) disable iff (reset)
        (enable && (count == 3'b111)) |=> (count == 3'b000)
    );

endmodule