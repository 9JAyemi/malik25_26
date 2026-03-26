module up_counter_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] count,
    input logic overflow
);

    // Reset clears count by the next clock sample.
    check_reset_clears_count: assert property (
        @(posedge clk)
        rst |=> (count == 4'h0)
    );

    // Reset clears overflow by the next clock sample.
    check_reset_clears_overflow: assert property (
        @(posedge clk)
        rst |=> (overflow == 1'b0)
    );

    // Overflow is asserted exactly at terminal count.
    check_overflow_matches_terminal_count: assert property (
        @(posedge clk) disable iff (rst)
        (overflow == (count == 4'hf))
    );

    // Count either increments or is asynchronously reset to zero.
    check_count_moves_by_one_or_resets: assert property (
        @(posedge clk) disable iff (rst)
        1'b1 |=> ((count == 4'h0) || (count == ($past(count) + 4'h1)))
    );

    // Terminal count wraps to zero on the next clock.
    check_terminal_count_wraps: assert property (
        @(posedge clk) disable iff (rst)
        (count == 4'hf) |=> (count == 4'h0)
    );

    // Overflow clears after the terminal count cycle.
    check_overflow_is_one_cycle_pulse: assert property (
        @(posedge clk) disable iff (rst)
        overflow |=> (!overflow)
    );

    // Counts below 14 cannot produce overflow on the next clock.
    check_no_overflow_below_14: assert property (
        @(posedge clk) disable iff (rst)
        (count < 4'he) |=> (!overflow)
    );

endmodule