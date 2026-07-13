module binary_counter_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] count
);

    // Reset drives the counter to zero on the following sampled cycle.
    check_reset_clears_count: assert property (
        @(posedge clk) rst |=> (count == 4'b0000)
    );

    // The count is zero on the cycle reset is released.
    check_reset_release_observes_zero: assert property (
        @(posedge clk) disable iff (rst) $fell(rst) |-> (count == 4'b0000)
    );

    // One cycle after reset is released, the counter has incremented to one.
    check_first_post_reset_increment: assert property (
        @(posedge clk) $fell(rst) |=> (count == 4'b0001)
    );

    // Without reset, the counter increments by one when below 15.
    check_count_increments_non_wrap: assert property (
        @(posedge clk) disable iff (rst)
        (!$past(rst) && ($past(count) != 4'hF)) |-> (count == ($past(count) + 4'd1))
    );

    // Without reset, the counter wraps from 15 back to zero.
    check_count_wraps_to_zero: assert property (
        @(posedge clk) disable iff (rst)
        (!$past(rst) && ($past(count) == 4'hF)) |-> (count == 4'b0000)
    );

endmodule