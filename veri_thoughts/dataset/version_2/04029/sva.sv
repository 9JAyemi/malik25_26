module ClockDivider_sva (
    input logic [31:0] Divisor,
    input logic        clkOut,
    input logic [31:0] count,
    input logic        clk,
    input logic        rst
);

    // Reset drives count to zero.
    check_reset_count_zero: assert property (
        @(posedge clk) rst |-> (count == 32'd0)
    );

    // Reset drives clkOut low.
    check_reset_clkout_zero: assert property (
        @(posedge clk) rst |-> (clkOut == 1'b0)
    );

    // Terminal count wraps back to zero on the next clock.
    check_count_wrap_on_terminal: assert property (
        @(posedge clk) disable iff (rst)
        ($signed({1'b0, count}) == ($signed({1'b0, Divisor}) - 33'sd1)) |=> (count == 32'd0)
    );

    // Non-terminal count increments by one on the next clock.
    check_count_increment_otherwise: assert property (
        @(posedge clk) disable iff (rst)
        !($signed({1'b0, count}) == ($signed({1'b0, Divisor}) - 33'sd1)) |=> (count == ($past(count) + 32'd1))
    );

    // Terminal count causes clkOut to toggle on the next clock.
    check_clkout_toggle_on_terminal: assert property (
        @(posedge clk) disable iff (rst)
        ($signed({1'b0, count}) == ($signed({1'b0, Divisor}) - 33'sd1)) |=> (clkOut != $past(clkOut))
    );

    // Non-terminal count leaves clkOut unchanged on the next clock.
    check_clkout_hold_otherwise: assert property (
        @(posedge clk) disable iff (rst)
        !($signed({1'b0, count}) == ($signed({1'b0, Divisor}) - 33'sd1)) |=> (clkOut == $past(clkOut))
    );

endmodule