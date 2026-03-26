module up_counter_sva (
    input logic       clk,
    input logic       rst,
    input logic [3:0] count,
    input logic       overflow
);

    // Reset drives count to zero on the next clock.
    check_reset_clears_count: assert property (
        @(posedge clk) disable iff ($initstate)
        rst |=> (count == 4'h0)
    );

    // Reset clears overflow on the next clock.
    check_reset_clears_overflow: assert property (
        @(posedge clk) disable iff ($initstate)
        rst |=> (overflow == 1'b0)
    );

    // A non-max count increments by one.
    check_count_increments_below_max: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (count != 4'hF) |=> (count == ($past(count) + 4'h1))
    );

    // A non-max count keeps overflow low.
    check_overflow_low_below_max: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (count != 4'hF) |=> (overflow == 1'b0)
    );

    // A max count wraps back to zero.
    check_count_wraps_at_max: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (count == 4'hF) |=> (count == 4'h0)
    );

    // A max count raises overflow.
    check_overflow_asserts_at_max: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (count == 4'hF) |=> (overflow == 1'b1)
    );

    // Overflow is only asserted when count is zero.
    check_overflow_implies_zero_count: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        overflow |-> (count == 4'h0)
    );

    // Overflow only follows a previous max count.
    check_overflow_implies_previous_max: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        overflow |-> ($past(count) == 4'hF)
    );

endmodule