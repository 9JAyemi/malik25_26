module binary_counter_sva #(parameter COUNTER_WIDTH = 8) (
    input logic clk,
    input logic rst,
    input logic [COUNTER_WIDTH-1:0] count
);

    // A sampled reset clears the counter by the next clock.
    check_reset_clears_count: assert property (
        @(posedge clk) rst |=> (count == '0)
    );

    // The counter stays zero while reset is held across cycles.
    check_reset_holds_zero: assert property (
        @(posedge clk) (rst && $past(rst)) |-> (count == '0)
    );

    // The first cycle after reset deassertion shows a cleared count.
    check_post_reset_count_zero: assert property (
        @(posedge clk) disable iff (rst) $past(rst) |-> (count == '0)
    );

    // In consecutive non-reset cycles, the counter increments by one.
    check_count_increments: assert property (
        @(posedge clk) disable iff (rst) !$past(rst) |-> (count == $past(count) + 1'b1)
    );

    // A maximum count value wraps back to zero on the next non-reset cycle.
    check_count_wraps_to_zero: assert property (
        @(posedge clk) disable iff (rst)
            (!$past(rst) && ($past(count) == {COUNTER_WIDTH{1'b1}})) |-> (count == '0)
    );

endmodule