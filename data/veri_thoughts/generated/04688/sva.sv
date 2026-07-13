module segClkDevider_sva (
    input logic        clk,
    input logic        rst,
    input logic        clk_div,
    input logic [31:0] count
);

    localparam logic [31:0] constantNumber = 32'd10000;

    // Reset clears both state elements by the next sampled clock.
    check_reset_clears_state: assert property (
        @(posedge clk) rst |=> (count == 32'd0) && (clk_div == 1'b0)
    );

    // Terminal count wraps back to zero.
    check_count_wraps_at_terminal: assert property (
        @(posedge clk) disable iff (rst)
        (count == (constantNumber - 32'd1)) |=> (count == 32'd0)
    );

    // Non-terminal count either increments or is asynchronously cleared.
    check_count_increments_or_clears: assert property (
        @(posedge clk) disable iff (rst)
        (count != (constantNumber - 32'd1)) |=> ((count == ($past(count) + 32'd1)) || (count == 32'd0))
    );

    // Terminal count makes clk_div toggle, unless async reset clears it low.
    check_clk_div_toggles_or_clears_at_terminal: assert property (
        @(posedge clk) disable iff (rst)
        (count == (constantNumber - 32'd1)) |=> ((clk_div == ~$past(clk_div)) || (clk_div == 1'b0))
    );

    // Below terminal count, a low clk_div must remain low.
    check_clk_div_low_holds_below_terminal: assert property (
        @(posedge clk) disable iff (rst)
        (count != (constantNumber - 32'd1) && (clk_div == 1'b0)) |=> (clk_div == 1'b0)
    );

    // At terminal count, a high clk_div must go low on the next cycle.
    check_clk_div_high_goes_low_at_terminal: assert property (
        @(posedge clk) disable iff (rst)
        (count == (constantNumber - 32'd1) && (clk_div == 1'b1)) |=> (clk_div == 1'b0)
    );

endmodule