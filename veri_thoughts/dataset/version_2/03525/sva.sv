module counter_assertions (
    input logic       rst,
    input logic       clk,
    input logic [2:0] count
);

    // A high reset on the previous clock drives count to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) disable iff ($initstate)
        $past(rst) |-> (count == 3'd0)
    );

    // With no reset in consecutive cycles, count increments by one.
    check_count_increments: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        !$past(rst) |-> (count == ($past(count) + 3'd1))
    );

    // A non-reset cycle after 7 wraps count back to zero.
    check_count_wraps: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (!$past(rst) && ($past(count) == 3'd7)) |-> (count == 3'd0)
    );

endmodule