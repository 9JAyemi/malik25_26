module binary_counter_sva (
    input logic       clk,
    input logic       reset,
    input logic       enable,
    input logic [3:0] count
);

    // Reset forces the counter to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 4'b0000)
    );

    // When enabled below 15, the counter increments by one.
    check_increment_when_enabled: assert property (
        @(posedge clk) disable iff (reset)
        (enable && (count != 4'b1111)) |=> (count == ($past(count) + 4'b0001))
    );

    // When disabled, the counter holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        (!enable) |=> (count == $past(count))
    );

    // At 15, the counter holds even if enable is asserted.
    check_hold_at_terminal_count: assert property (
        @(posedge clk) disable iff (reset)
        (enable && (count == 4'b1111)) |=> (count == $past(count))
    );

    // Outside reset, the counter never decreases.
    check_count_monotonic_without_reset: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (count >= $past(count))
    );

endmodule