module ClockDivider_sva (
    input logic [31:0] Divisor,
    input logic        clkOut,
    input logic [31:0] count,
    input logic        clk,
    input logic        rst
);

    // Reset forces both registered outputs low.
    check_reset_clears_outputs: assert property (
        @(posedge clk) rst |-> (count == 32'd0 && clkOut == 1'b0)
    );

    // A terminal count reloads the counter to zero.
    check_count_reloads_on_terminal_count: assert property (
        @(posedge clk) disable iff (rst)
        (count == (Divisor - 32'd1)) |=> (count == 32'd0)
    );

    // A non-terminal count increments by one.
    check_count_increments_on_nonterminal_count: assert property (
        @(posedge clk) disable iff (rst)
        (count != (Divisor - 32'd1)) |=> (count == ($past(count) + 32'd1))
    );

    // A terminal count toggles the clock output.
    check_clkout_toggles_on_terminal_count: assert property (
        @(posedge clk) disable iff (rst)
        (count == (Divisor - 32'd1)) |=> (clkOut == ~$past(clkOut))
    );

    // A non-terminal count holds the clock output.
    check_clkout_holds_on_nonterminal_count: assert property (
        @(posedge clk) disable iff (rst)
        (count != (Divisor - 32'd1)) |=> (clkOut == $past(clkOut))
    );

    // The clock output can only change after a terminal count.
    check_clkout_changes_only_after_terminal_count: assert property (
        @(posedge clk) disable iff (rst)
        $changed(clkOut) |-> ($past(count) == ($past(Divisor) - 32'd1))
    );

endmodule