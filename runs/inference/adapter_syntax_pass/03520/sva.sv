module counter_sva (
    input logic clk,
    input logic rst,
    input logic [7:0] count
);

    // Reset forces the counter to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) rst |-> (count == 8'h00)
    );

    // The first sampled cycle after reset deassertion still shows zero.
    check_post_reset_zero: assert property (
        @(posedge clk) disable iff (rst) $fell(rst) |-> (count == 8'h00)
    );

    // The first active cycle after reset deassertion increments to one.
    check_post_reset_increment: assert property (
        @(posedge clk) disable iff (rst) $fell(rst) |=> (count == 8'h01)
    );

    // The counter increments by one on each active clock.
    check_count_increments: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> (count == ($past(count) + 8'd1))
    );

    // The 8-bit counter wraps from 255 back to 0.
    check_count_wraps: assert property (
        @(posedge clk) disable iff (rst) (count == 8'hFF) |=> (count == 8'h00)
    );

endmodule