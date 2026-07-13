module counter_sva #(
    parameter int unsigned MAX_COUNT = 255
) (
    input logic       clk,
    input logic       rst,
    input logic [7:0] count
);

    // A reset cycle clears count to zero by the next clock.
    check_reset_clears_count: assert property (
        @(posedge clk)
        rst |=> (count == 8'd0)
    );

    // On the first cycle after reset deasserts, count is still zero.
    check_reset_release_sees_zero: assert property (
        @(posedge clk)
        $fell(rst) |-> (count == 8'd0)
    );

    // When below MAX_COUNT, count increments by one on the next clock.
    check_count_increments_below_max: assert property (
        @(posedge clk) disable iff (rst)
        (count != MAX_COUNT) |=> (count == ($past(count) + 8'd1))
    );

    // When at MAX_COUNT, count wraps to zero on the next clock.
    check_count_wraps_at_max: assert property (
        @(posedge clk) disable iff (rst)
        (count == MAX_COUNT) |=> (count == 8'd0)
    );

endmodule