module binary_counter_sva (
    input logic       clk,
    input logic       reset,
    input logic [3:0] count
);

// Reset drives count to zero on the next clock.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 4'h0)
    );

// When not at max, count increments by one on the next clock.
    check_count_increments: assert property (
        @(posedge clk) disable iff (reset)
        (count != 4'hF) |=> (count == ($past(count) + 4'h1))
    );

// When at max, count wraps to zero on the next clock.
    check_count_wraps: assert property (
        @(posedge clk) disable iff (reset)
        (count == 4'hF) |=> (count == 4'h0)
    );

endmodule
