module sync_reset_counter_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] count
);

    // Active-low reset forces count to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) !rst |-> (count == 4'h0)
    );

    // On the first clock after reset deasserts, count is still zero.
    check_post_reset_starts_from_zero: assert property (
        @(posedge clk) disable iff (!rst) $rose(rst) |-> (count == 4'h0)
    );

    // When not in reset, count increments by one each clock.
    check_count_increments: assert property (
        @(posedge clk) disable iff (!rst) 1'b1 |=> (count == ($past(count) + 4'd1))
    );

    // When not in reset, count wraps from 15 back to 0.
    check_count_wraps_from_max: assert property (
        @(posedge clk) disable iff (!rst) (count == 4'hF) |=> (count == 4'h0)
    );

endmodule