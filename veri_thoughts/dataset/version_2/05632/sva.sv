module counter_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] count
);

    // Reset forces count to zero on the next clock.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 4'd0)
    );

    // The first cycle after reset deassertion still observes zero.
    check_post_reset_zero: assert property (
        @(posedge clk) disable iff ($initstate)
        ($past(reset) && !reset) |-> (count == 4'd0)
    );

    // Outside reset, count increments by one each cycle.
    check_count_increments: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        !$past(reset) |-> (count == ($past(count) + 4'd1))
    );

    // The 4-bit counter wraps from 15 back to 0.
    check_count_wraps_from_max: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        (!$past(reset) && ($past(count) == 4'hF)) |-> (count == 4'd0)
    );

endmodule