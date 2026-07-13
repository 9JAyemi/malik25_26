module counter_sva (
    input logic       clk,
    input logic       rst,
    input logic [3:0] count
);

    // Reset drives count to zero on the next sampled cycle.
    check_reset_clears_count: assert property (
        @(posedge clk) rst |=> (count == 4'd0)
    );

    // Count stays zero while reset remains asserted.
    check_count_held_in_reset: assert property (
        @(posedge clk) (rst && $past(rst)) |-> (count == 4'd0)
    );

    // Outside reset, count increments by one each cycle.
    check_count_increments: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> (count == ($past(count) + 4'd1))
    );

    // Outside reset, the maximum count value wraps to zero.
    check_count_wraps_after_max: assert property (
        @(posedge clk) disable iff (rst) (count == 4'hF) |=> (count == 4'h0)
    );

    // On reset release, the observed count is still zero.
    check_count_zero_after_reset_release: assert property (
        @(posedge clk) disable iff (rst) $fell(rst) |-> (count == 4'd0)
    );

endmodule