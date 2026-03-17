module counter_sva (
    input logic       reset,
    input logic       clk,
    input logic [7:0] count
);

    // Reset drives the counter to zero on the following clock.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 8'd0)
    );

    // When below 255 and not in reset, the counter increments by one.
    check_count_increments: assert property (
        @(posedge clk) disable iff (reset)
        (count != 8'hFF) |=> (count == ($past(count) + 8'd1))
    );

    // When at 255 and not in reset, the counter wraps to zero.
    check_count_wraps_to_zero: assert property (
        @(posedge clk) disable iff (reset)
        (count == 8'hFF) |=> (count == 8'd0)
    );

endmodule