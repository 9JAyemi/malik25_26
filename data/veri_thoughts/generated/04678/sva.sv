module clk_divider_sva (
    input logic clk,
    input logic slower_clk,
    input logic [24:0] counter
);

    // Non-terminal count increments by one on the next clock.
    check_counter_increments: assert property (
        @(posedge clk)
        (counter != 25'd1250000) |=> (counter == ($past(counter) + 25'd1))
    );

    // slower_clk holds its value when the terminal count is not reached.
    check_slower_clk_holds_between_toggles: assert property (
        @(posedge clk)
        (counter != 25'd1250000) |=> (slower_clk == $past(slower_clk))
    );

    // Terminal count forces the counter back to zero on the next clock.
    check_counter_resets_at_terminal_count: assert property (
        @(posedge clk)
        (counter == 25'd1250000) |=> (counter == 25'd0)
    );

    // Terminal count toggles slower_clk on the next clock.
    check_slower_clk_toggles_at_terminal_count: assert property (
        @(posedge clk)
        (counter == 25'd1250000) |=> (slower_clk == ~$past(slower_clk))
    );

endmodule

bind clk_divider clk_divider_sva clk_divider_sva_i (
    .clk(clk),
    .slower_clk(slower_clk),
    .counter(counter)
);