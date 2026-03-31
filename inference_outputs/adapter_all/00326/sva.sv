module binary_counter_sva #(
    parameter int N = 4
) (
    input logic clk,
    input logic reset,
    input logic [N-1:0] count
);

    // Reset drives the counter to zero on the next clock.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == '0)
    );

    // When not in reset, the counter increments by one each cycle.
    check_count_increments: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |=> (count == ($past(count) + 1'b1))
    );

    // A maximum count value wraps back to zero on the next clock.
    check_count_wraps: assert property (
        @(posedge clk) disable iff (reset) (count == {N{1'b1}}) |=> (count == '0)
    );

endmodule