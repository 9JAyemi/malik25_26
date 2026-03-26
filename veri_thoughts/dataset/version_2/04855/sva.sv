module counter_sva (
    input logic       clk,
    input logic       reset,
    input logic [3:0] count
);

    // A reset cycle forces count to zero on the following clock.
    check_reset_clears_count: assert property (
        @(posedge clk) disable iff (reset)
        $past(reset) |-> (count == 4'd0)
    );

    // Without reset, count increments by one when below the maximum value.
    check_count_increments_no_wrap: assert property (
        @(posedge clk) disable iff (reset)
        (!$past(reset) && ($past(count) < 4'hF)) |-> (count == ($past(count) + 4'd1))
    );

    // Without reset, count wraps from 15 back to zero.
    check_count_wraps_to_zero: assert property (
        @(posedge clk) disable iff (reset)
        (!$past(reset) && ($past(count) == 4'hF)) |-> (count == 4'd0)
    );

endmodule