module counter_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] count
);

    // A reset cycle forces the counter to zero.
    reset_clears_count: assert property (
        @(posedge clk) rst |=> (count == 4'd0)
    );

    // While reset stays asserted, the counter remains zero.
    reset_holds_count_zero: assert property (
        @(posedge clk) disable iff ($initstate)
        (rst && $past(rst)) |-> (count == 4'd0)
    );

    // The first sampled cycle after reset shows a zero count.
    post_reset_count_zero: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        $past(rst) |-> (count == 4'd0)
    );

    // Out of reset, the counter increments by one each cycle.
    count_increments_by_one: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        !$past(rst) |-> (count == ($past(count) + 4'd1))
    );

    // A running count wraps from 15 back to 0.
    count_wraps_after_max: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (!$past(rst) && ($past(count) == 4'hF)) |-> (count == 4'h0)
    );

endmodule