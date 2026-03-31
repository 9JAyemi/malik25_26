module binary_counter_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] count
);

    // Reset forces count to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) rst |-> (count == 4'd0)
    );

    // On the cycle reset deasserts, count is still zero.
    check_reset_release_starts_from_zero: assert property (
        @(posedge clk) $fell(rst) |-> (count == 4'd0)
    );

    // When not in reset, count increments by one each cycle.
    check_count_increments: assert property (
        @(posedge clk) disable iff (rst) count == $past(count) + 4'd1
    );

    // When not in reset, count wraps from 15 back to 0.
    check_count_wraps_from_max: assert property (
        @(posedge clk) disable iff (rst) (count == 4'hF) |-> (count == 4'h0)
    );

endmodule