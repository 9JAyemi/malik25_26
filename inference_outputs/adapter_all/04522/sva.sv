module binary_counter_sva (
    input logic       clk,
    input logic       reset,
    input logic [3:0] count
);

    // Reset forces the counter to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |-> (count == 4'b0000)
    );

    // A non-maximum count increments by one on the next clock.
    check_count_increments: assert property (
        @(posedge clk) disable iff (reset)
        (count != 4'hF) |=> (count == ($past(count) + 4'h1))
    );

    // A maximum count wraps back to zero on the next clock.
    check_count_wraps: assert property (
        @(posedge clk) disable iff (reset)
        (count == 4'hF) |=> (count == 4'h0)
    );

endmodule