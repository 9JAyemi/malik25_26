module binary_counter_sva (
    input logic       clk,
    input logic       reset,
    input logic [3:0] count
);

    // A sampled reset forces the counter to be zero by the next clock.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 4'b0000)
    );

    // A terminal count wraps back to zero on the next clock.
    check_wrap_from_max_count: assert property (
        @(posedge clk) disable iff (reset)
        (count == 4'b1111) |=> (count == 4'b0000)
    );

    // A non-terminal count advances by one unless an asynchronous reset drives it to zero.
    check_increment_from_nonmax_or_async_reset: assert property (
        @(posedge clk) disable iff (reset)
        (count != 4'b1111) |=> ((count == ($past(count) + 4'b0001)) || (count == 4'b0000))
    );

endmodule