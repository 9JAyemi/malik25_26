module four_bit_counter_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] count
);

    // Reset forces the counter to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |-> (count == 4'd0)
    );

    // The first sampled cycle after reset deassertion still shows zero.
    check_post_reset_zero: assert property (
        @(posedge clk) disable iff (reset) $fell(reset) |-> (count == 4'd0)
    );

    // The first active cycle after reset deassertion increments to one.
    check_post_reset_increment: assert property (
        @(posedge clk) disable iff (reset) $fell(reset) |=> (count == 4'd1)
    );

    // The counter increments by one on each active clock.
    check_count_increments: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |=> (count == ($past(count) + 4'd1))
    );

    // The 4-bit counter wraps from 15 back to 0.
    check_count_wraps: assert property (
        @(posedge clk) disable iff (reset) (count == 4'hF) |=> (count == 4'h0)
    );

endmodule