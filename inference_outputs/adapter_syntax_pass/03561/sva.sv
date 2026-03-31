module freq_divider_sva #(
    parameter int unsigned n = 2
) (
    input logic clk_in,
    input logic clk_out,
    input logic [31:0] count
);

    // Count increments by one when it is not at the terminal count.
    check_count_increments_below_terminal: assert property (
        @(posedge clk_in)
        (count != (n - 32'd1)) |=> (count == ($past(count) + 32'd1))
    );

    // Count wraps to zero after reaching the terminal count.
    check_count_wraps_at_terminal: assert property (
        @(posedge clk_in)
        (count == (n - 32'd1)) |=> (count == 32'd0)
    );

    // clk_out holds its value when the terminal count is not reached.
    check_clk_out_holds_below_terminal: assert property (
        @(posedge clk_in)
        (count != (n - 32'd1)) |=> (clk_out == $past(clk_out))
    );

    // clk_out toggles when the terminal count is reached.
    check_clk_out_toggles_at_terminal: assert property (
        @(posedge clk_in)
        (count == (n - 32'd1)) |=> (clk_out != $past(clk_out))
    );

endmodule