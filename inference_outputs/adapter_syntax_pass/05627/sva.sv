module counter4_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] count
);

    // Reset forces the counter to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) rst |-> (count == 4'h0)
    );

    // The first sampled cycle after reset deassertion still shows zero.
    check_post_reset_zero: assert property (
        @(posedge clk) disable iff (rst) $fell(rst) |-> (count == 4'h0)
    );

    // The counter increments by one when below 9.
    check_increment_when_below_nine: assert property (
        @(posedge clk) disable iff (rst) (count != 4'h9) |=> (count == ($past(count) + 4'd1))
    );

    // The counter wraps from 9 back to 0.
    check_wrap_from_nine_to_zero: assert property (
        @(posedge clk) disable iff (rst) (count == 4'h9) |=> (count == 4'h0)
    );

    // The counter value never exceeds 9.
    check_count_range: assert property (
        @(posedge clk) disable iff (rst) (count <= 4'h9)
    );

endmodule