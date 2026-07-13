module clock_divider_sva #(
    parameter integer divide_by = 2
) (
    input logic        clk_in,
    input logic        reset,
    input logic        clk_out,
    input logic [31:0] counter
);

    // Reset clears the counter by the next sampled clock.
    check_reset_clears_counter: assert property (
        @(posedge clk_in) reset |=> (counter == 32'd0)
    );

    // Reset drives clk_out low by the next sampled clock.
    check_reset_clears_clk_out: assert property (
        @(posedge clk_in) reset |=> (clk_out == 1'b0)
    );

    // Terminal count resets the counter on the following clock.
    check_terminal_count_resets_counter: assert property (
        @(posedge clk_in) disable iff (reset)
        (counter == divide_by - 1) |=> (counter == 32'd0)
    );

    // Terminal count toggles clk_out on the following clock.
    check_terminal_count_toggles_clk_out: assert property (
        @(posedge clk_in) disable iff (reset)
        (counter == divide_by - 1) |=> (clk_out == ~$past(clk_out))
    );

    // Non-terminal count increments the counter by one.
    check_nonterminal_count_increments_counter: assert property (
        @(posedge clk_in) disable iff (reset)
        (counter != divide_by - 1) |=> (counter == ($past(counter) + 32'd1))
    );

    // Non-terminal count holds clk_out steady.
    check_nonterminal_count_holds_clk_out: assert property (
        @(posedge clk_in) disable iff (reset)
        (counter != divide_by - 1) |=> (clk_out == $past(clk_out))
    );

endmodule