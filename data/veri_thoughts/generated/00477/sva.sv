module counter_sva (
    input logic       clk,
    input logic       reset,
    input logic [3:0] count
);

    // Count must be zero whenever reset is asserted.
    check_reset_clears_count: assert property (
        @(posedge clk) !reset |-> (count == 4'd0)
    );

    // Count is still zero on the first sampled cycle after reset was low.
    check_post_reset_sample_is_zero: assert property (
        @(posedge clk) disable iff (!reset)
        $past(!reset) |-> (count == 4'd0)
    );

    // After a reset-high cycle, count either increments or was asynchronously cleared to zero.
    check_count_increments_or_async_clears: assert property (
        @(posedge clk) disable iff (!reset)
        $past(reset) |-> ((count == 4'd0) || (count == ($past(count) + 4'd1)))
    );

endmodule