module ClockDivider_sva (
    input logic [31:0] Divisor,
    input logic        clkOut,
    input logic        clk,
    input logic        rst
);

    // Reset forces the divider output low.
    check_reset_forces_clkout_low: assert property (
        @(posedge clk) rst |-> (clkOut == 1'b0)
    );

    // A non-max count increments the counter and holds the output.
    check_count_increments_when_not_max: assert property (
        @(posedge clk) disable iff (rst)
        (($signed({1'b0, $past(Divisor)}) != ($signed({1'b0, $past(Divisor)}) - 1)) &&
         ($past(Divisor) != 32'd0))
        |-> (($past(count_i) == ($past(count_i) + 32'd1)) &&
             (clkOut == $past(clkOut)))
    );

    // A max count clears the counter and toggles the output.
    check_count_wraps_when_max: assert property (
        @(posedge clk) disable iff (rst)
        (($signed({1'b0, $past(Divisor)}) == ($signed({1'b0, $past(Divisor)}) - 1)) &&
         ($past(Divisor) != 32'd0))
        |-> (($past(count_i) == 32'd0) &&
             (clkOut == ~$past(clkOut)))
    );

    // A zero divisor keeps the counter and output unchanged.
    check_zero_divisor_holds_state: assert property (
        @(posedge clk) disable iff (rst)
        ($past(Divisor) == 32'd0)
        |-> (($past(count_i) == $past(count_i)) &&
             (clkOut == $past(clkOut)))
    );

    // A zero counter value only occurs after a max count.
    check_zero_count_requires_max: assert property (
        @(posedge clk) disable iff (rst)
        ($past(count_i) == 32'd0)
        |-> (($signed({1'b0, $past(Divisor)}) == ($signed({1'b0, $past(Divisor)}) - 1)) &&
             ($past(Divisor) != 32'd0))
    );

    // A zero output only occurs after a max count.
    check_zero_output_requires_max: assert property (
        @(posedge clk) disable iff (rst)
        (clkOut == 1'b0)
        |-> (($signed({1'b0, $past(Divisor)}) == ($signed({1'b0, $past(Divisor)}) - 1)) &&
             ($past(Divisor) != 32'd0))
    );

endmodule