module binary_counter_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] count
);

    // Reset forces the counter to zero on the next clock.
    check_reset_clears_count: assert property (
        @(posedge clk) rst |=> (count == 4'h0)
    );

    // The first clock after reset deassertion still shows zero.
    check_post_reset_zero: assert property (
        @(posedge clk) disable iff (rst) $fell(rst) |-> (count == 4'h0)
    );

    // The first non-reset clock after reset deassertion increments to one.
    check_post_reset_increment: assert property (
        @(posedge clk) disable iff (rst) $fell(rst) |=> (count == 4'h1)
    );

    // The counter increments by one on each non-reset clock.
    check_count_increments: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> (count == ($past(count) + 4'd1))
    );

    // The 4-bit counter wraps from 15 back to 0.
    check_count_wraps: assert property (
        @(posedge clk) disable iff (rst) (count == 4'hF) |=> (count == 4'h0)
    );

endmodule