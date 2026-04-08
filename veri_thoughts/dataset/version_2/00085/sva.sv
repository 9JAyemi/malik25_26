module binary_counter_sva (
    input logic       clk,
    input logic       reset,
    input logic [3:0] count
);

    // Reset forces the counter to zero on the following clock sample.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 4'h0)
    );

    // When below 15 and not in reset, the counter increments by one.
    check_increment_when_not_max: assert property (
        @(posedge clk) disable iff (reset)
        (count != 4'hF) |=> (count == ($past(count) + 4'h1))
    );

    // When at 15 and not in reset, the counter wraps to zero.
    check_wrap_from_max: assert property (
        @(posedge clk) disable iff (reset)
        (count == 4'hF) |=> (count == 4'h0)
    );

    // On every non-reset cycle, the counter value changes.
    check_count_changes_each_cycle: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (count != $past(count))
    );

endmodule