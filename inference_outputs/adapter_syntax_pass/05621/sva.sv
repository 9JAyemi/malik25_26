module ClockDivider_sva (
    input logic [31:0] Divisor,
    input logic        clkOut,
    input logic [31:0] count,
    input logic        clk,
    input logic        rst
);

    // Reset clears the counter to zero.
    check_count_clears_on_reset: assert property (
        @(posedge clk) rst |-> (count == 32'd0)
    );

    // Reset clears the clock output.
    check_clkout_clears_on_reset: assert property (
        @(posedge clk) rst |-> (clkOut == 1'b0)
    );

    // The counter increments by one when it is not at the terminal count.
    check_count_increments_below_terminal: assert property (
        @(posedge clk) disable iff (rst)
        (($signed({1'b0, count}) != ($signed({1'b0, Divisor}) - 32'sd1))) |=> (count == ($past(count) + 32'd1))
    );

    // The counter wraps to zero at the terminal count.
    check_count_wraps_at_terminal: assert property (
        @(posedge clk) disable iff (rst)
        (($signed({1'b0, count}) == ($signed({1'b0, Divisor}) - 32'sd1))) |=> (count == 32'd0)
    );

    // The clock output holds when the counter is not at the terminal count.
    check_clkout_holds_below_terminal: assert property (
        @(posedge clk) disable iff (rst)
        (($signed({1'b0, count}) != ($signed({1'b0, Divisor}) - 32'sd1))) |=> (clkOut == $past(clkOut))
    );

    // The clock output toggles when the counter is at the terminal count.
    check_clkout_toggles_at_terminal: assert property (
        @(posedge clk) disable iff (rst)
        (($signed({1'b0, count}) == ($signed({1'b0, Divisor}) - 32'sd1))) |=> (clkOut == ~$past(clkOut))
    );

endmodule