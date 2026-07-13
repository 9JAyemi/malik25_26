module ClockDivider_sva (
    input logic [31:0] Divisor,
    input logic        clkOut,
    input logic        clk,
    input logic        rst,
    input logic [31:0] count_i,
    input logic        clkOut_i
);

    // Reset clears the counter.
    check_count_reset: assert property (
        @(posedge clk) rst |-> (count_i == 32'd0)
    );

    // Reset clears the output flip-flop.
    check_clkout_reset: assert property (
        @(posedge clk) rst |-> (clkOut_i == 1'b0)
    );

    // The output is a direct reflection of the internal flip-flop.
    check_clkout_matches_internal: assert property (
        @(posedge clk) disable iff (rst) (clkOut == clkOut_i)
    );

    // The counter increments when it is not at the terminal count.
    check_count_increments: assert property (
        @(posedge clk) disable iff (rst)
        (($signed({1'b0, count_i}) != ($signed({1'b0, Divisor}) - 32'sd1))) |=> (count_i == ($past(count_i) + 32'd1))
    );

    // The counter wraps to zero at the terminal count.
    check_count_wraps: assert property (
        @(posedge clk) disable iff (rst)
        (($signed({1'b0, count_i}) == ($signed({1'b0, Divisor}) - 32'sd1))) |=> (count_i == 32'd0)
    );

    // The output holds when the counter is not at the terminal count.
    check_clkout_holds: assert property (
        @(posedge clk) disable iff (rst)
        (($signed({1'b0, count_i}) != ($signed({1'b0, Divisor}) - 32'sd1))) |=> (clkOut_i == $past(clkOut_i))
    );

    // The output toggles when the counter is at the terminal count.
    check_clkout_toggles: assert property (
        @(posedge clk) disable iff (rst)
        (($signed({1'b0, count_i}) == ($signed({1'b0, Divisor}) - 32'sd1))) |=> (clkOut_i == ~$past(clkOut_i))
    );

endmodule