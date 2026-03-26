module GrayCounter_sva #(
    parameter int unsigned CLK_DIV = 17_000_000
) (
    input logic       clk,
    input logic       incdec,
    input logic       stop,
    input logic       rst,
    input logic [7:0] gray,
    input logic [7:0] normal,
    input logic [31:0] clkDiv
);

    localparam logic [31:0] PRE_TERMINAL = CLK_DIV - 1;

    // Reset clears the divider and numeric count on the next cycle.
    check_reset_clears_state: assert property (
        @(posedge clk) disable iff ($initstate)
        rst |=> (clkDiv == 32'd0 && normal == 8'd0)
    );

    // Stop holds both the divider and numeric count.
    check_stop_holds_state: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        stop |=> (clkDiv == $past(clkDiv) && normal == $past(normal))
    );

    // While running below terminal count, the divider increments by one.
    check_divider_increments_while_running: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (!stop && (clkDiv != PRE_TERMINAL)) |=> (clkDiv == ($past(clkDiv) + 32'd1))
    );

    // At terminal count, the divider rolls back to zero.
    check_divider_rolls_over_at_terminal: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (!stop && (clkDiv == PRE_TERMINAL)) |=> (clkDiv == 32'd0)
    );

    // At terminal count with incdec high, the numeric count increments.
    check_count_increments_at_terminal: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (!stop && (clkDiv == PRE_TERMINAL) && incdec) |=> (normal == ($past(normal) + 8'd1))
    );

    // At terminal count with incdec low, the numeric count decrements.
    check_count_decrements_at_terminal: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (!stop && (clkDiv == PRE_TERMINAL) && !incdec) |=> (normal == ($past(normal) - 8'd1))
    );

    // Below terminal count, the numeric count holds its value.
    check_count_holds_before_terminal: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (!stop && (clkDiv != PRE_TERMINAL)) |=> (normal == $past(normal))
    );

    // Gray output is the Gray-code of the previous cycle's numeric count.
    check_gray_tracks_previous_normal: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        gray == ($past(normal) ^ ($past(normal) >> 1))
    );

    // Any numeric count change must come from an enabled terminal divider cycle.
    check_count_change_only_at_terminal: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (!$past(rst) && (normal != $past(normal))) |-> (!$past(stop) && ($past(clkDiv) == PRE_TERMINAL))
    );

    // Any numeric count change must follow the previous incdec direction.
    check_count_change_matches_incdec: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (!$past(rst) && (normal != $past(normal))) |->
            (($past(incdec) && (normal == ($past(normal) + 8'd1))) ||
             (!$past(incdec) && (normal == ($past(normal) - 8'd1))))
    );

endmodule