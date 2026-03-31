module freq_divider_sva #(
    parameter int n = 2
) (
    input logic clk_in,
    input logic clk_out,
    input logic [31:0] count
);

    // Count increments by one when it is not at the terminal count.
    check_count_increments: assert property (
        @(posedge clk_in) disable iff ($initstate)
        (count != n-1) |=> (count == $past(count) + 32'd1)
    );

    // Count wraps to zero when it reaches the terminal count.
    check_count_wraps: assert property (
        @(posedge clk_in) disable iff ($initstate)
        (count == n-1) |=> (count == 32'd0)
    );

    // clk_out toggles when count reaches the terminal count.
    check_clk_out_toggles: assert property (
        @(posedge clk_in) disable iff ($initstate)
        (count == n-1) |=> (clk_out == ~$past(clk_out))
    );

    // clk_out holds its value when count is not at the terminal count.
    check_clk_out_holds: assert property (
        @(posedge clk_in) disable iff ($initstate)
        (count != n-1) |=> (clk_out == $past(clk_out))
    );

endmodule