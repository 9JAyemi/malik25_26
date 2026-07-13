module up_counter_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [2:0] count
);

    // Synchronous reset clears the counter on the next cycle.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 3'b000)
    );

    // Reset takes priority over enable.
    check_reset_priority_over_enable: assert property (
        @(posedge clk) (reset && enable) |=> (count == 3'b000)
    );

    // When enabled, the counter increments by one.
    check_increment_when_enabled: assert property (
        @(posedge clk) disable iff (reset)
        enable |=> (count == ($past(count) + 3'd1))
    );

    // When disabled, the counter holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        !enable |=> (count == $past(count))
    );

    // Incrementing from the maximum value wraps to zero.
    check_wrap_from_max: assert property (
        @(posedge clk) disable iff (reset)
        (enable && (count == 3'b111)) |=> (count == 3'b000)
    );

endmodule