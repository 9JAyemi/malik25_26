module clock_counter_assertions(
    input logic        clk_i,
    input logic        reset_n,
    input logic        clk_o,
    input logic [14:0] count
);

    // A sampled reset cycle clears the counter and output by the next clock.
    check_reset_clears_state: assert property (
        @(posedge clk_i)
        (!reset_n) |=> (count == 15'd0 && clk_o == 1'b0)
    );

    // Below the terminal count, the counter increments by one.
    check_count_increments_below_limit: assert property (
        @(posedge clk_i) disable iff (!reset_n)
        (count < 15'd1800) |=> (count == ($past(count) + 15'd1))
    );

    // Below the terminal count, the output clock holds its value.
    check_clk_holds_below_limit: assert property (
        @(posedge clk_i) disable iff (!reset_n)
        (count < 15'd1800) |=> (clk_o == $past(clk_o))
    );

    // At or above the terminal count, the counter wraps to zero.
    check_count_wraps_at_limit: assert property (
        @(posedge clk_i) disable iff (!reset_n)
        (count >= 15'd1800) |=> (count == 15'd0)
    );

    // At or above the terminal count, the output clock toggles.
    check_clk_toggles_at_limit: assert property (
        @(posedge clk_i) disable iff (!reset_n)
        (count >= 15'd1800) |=> (clk_o == ~$past(clk_o))
    );

endmodule