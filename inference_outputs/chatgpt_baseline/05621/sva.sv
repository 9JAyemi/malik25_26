module ClockDivider_assertions (
    input logic [31:0] Divisor,
    input logic        clkOut,
    input logic [31:0] count,
    input logic        clk,
    input logic        rst
);

    // Reset forces both outputs low.
    check_reset_clears_outputs: assert property (
        @(posedge clk) rst |-> (count == 32'd0) && (clkOut == 1'b0)
    );

    // One cycle after a sampled reset, outputs are still low before the next clock update.
    check_post_reset_outputs_still_low: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        $past(rst) |-> (count == 32'd0) && (clkOut == 1'b0)
    );

    // Terminal count causes the counter to wrap to zero.
    check_count_wrap_on_terminal: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        !$past(rst) &&
        ($signed({1'b0, $past(count)}) == ($signed({1'b0, $past(Divisor)}) - 33'sd1))
        |-> (count == 32'd0)
    );

    // Terminal count causes clkOut to toggle.
    check_clkout_toggle_on_terminal: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        !$past(rst) &&
        ($signed({1'b0, $past(count)}) == ($signed({1'b0, $past(Divisor)}) - 33'sd1))
        |-> (clkOut == !$past(clkOut))
    );

    // Non-terminal count increments by one.
    check_count_increment_on_nonterminal: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        !$past(rst) &&
        ($signed({1'b0, $past(count)}) != ($signed({1'b0, $past(Divisor)}) - 33'sd1))
        |-> (count == ($past(count) + 32'd1))
    );

    // Non-terminal count leaves clkOut unchanged.
    check_clkout_holds_on_nonterminal: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        !$past(rst) &&
        ($signed({1'b0, $past(count)}) != ($signed({1'b0, $past(Divisor)}) - 33'sd1))
        |-> (clkOut == $past(clkOut))
    );

endmodule