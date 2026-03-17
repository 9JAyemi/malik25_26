module frequency_divider_sva #(
    parameter int unsigned div = 10
) (
    input logic        clk_in,
    input logic        rst,
    input logic        clk_out,
    input logic [31:0] count
);

    localparam logic [31:0] DIV_MINUS_1 = div - 1;

    // Reset clears both count and clk_out.
    check_reset_clears_state: assert property (
        @(posedge clk_in) rst |-> ((count == 32'd0) && (clk_out == 1'b0))
    );

    // Count increments by one before reaching div-1.
    check_count_increments_before_wrap: assert property (
        @(posedge clk_in) disable iff (rst || $initstate)
        ($past(count) != DIV_MINUS_1) |-> (count == ($past(count) + 32'd1))
    );

    // clk_out holds its value before count reaches div-1.
    check_clk_out_holds_before_wrap: assert property (
        @(posedge clk_in) disable iff (rst || $initstate)
        ($past(count) != DIV_MINUS_1) |-> (clk_out == $past(clk_out))
    );

    // Count wraps to zero when the previous count was div-1.
    check_count_wraps_at_terminal: assert property (
        @(posedge clk_in) disable iff (rst || $initstate)
        ($past(count) == DIV_MINUS_1) |-> (count == 32'd0)
    );

    // clk_out toggles when the previous count was div-1.
    check_clk_out_toggles_at_terminal: assert property (
        @(posedge clk_in) disable iff (rst || $initstate)
        ($past(count) == DIV_MINUS_1) |-> (clk_out == ~$past(clk_out))
    );

    // clk_out can only change on a wrap cycle.
    check_clk_out_changes_only_on_wrap: assert property (
        @(posedge clk_in) disable iff (rst || $initstate)
        (clk_out != $past(clk_out)) |-> ($past(count) == DIV_MINUS_1)
    );

    // A zero count outside reset must come from a wrap cycle.
    check_zero_count_only_after_wrap: assert property (
        @(posedge clk_in) disable iff (rst || $initstate)
        (count == 32'd0) |-> ($past(count) == DIV_MINUS_1)
    );

endmodule