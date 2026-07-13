module ClockDivider_sva (
    input logic [31:0] Divisor,
    input logic clkOut,
    input logic [31:0] count,
    input logic clk,
    input logic rst
);

// Reset drives count to zero on the next clock.
    check_count_zero_on_reset: assert property (
        @(posedge clk) rst |=> (count == 32'd0)
    );

// Reset drives clkOut low on the next clock.
    check_clkout_low_on_reset: assert property (
        @(posedge clk) rst |=> (clkOut == 1'b0)
    );

// When count matches the divisor minus one, clkOut toggles.
    check_clkout_toggles_on_match: assert property (
        @(posedge clk) disable iff (rst)
        ($signed({1'b0, count}) == ($signed({1'b0, Divisor}) - 32'd1)) |=> (clkOut == ~$past(clkOut))
    );

// When count does not match the divisor minus one, clkOut holds.
    check_clkout_holds_when_no_match: assert property (
        @(posedge clk) disable iff (rst)
        ($signed({1'b0, count}) != ($signed({1'b0, Divisor}) - 32'd1)) |=> (clkOut == $past(clkOut))
    );

// When count matches the divisor minus one, count wraps to zero.
    check_count_wraps_on_match: assert property (
        @(posedge clk) disable iff (rst)
        ($signed({1'b0, count}) == ($signed({1'b0, Divisor}) - 32'd1)) |=> (count == 32'd0)
    );

// When count does not match the divisor minus one, count increments by one.
    check_count_increments_when_no_match: assert property (
        @(posedge clk) disable iff (rst)
        ($signed({1'b0, count}) != ($signed({1'b0, Divisor}) - 32'd1)) |=> (count == ($past(count) + 32'd1))
    );

// If clkOut is high and count matches the divisor minus one, next clkOut is low.
    check_clkout_low_when_count_matches: assert property (
        @(posedge clk) disable iff (rst)
        (clkOut && ($signed({1'b0, count}) == ($signed({1'b0, Divisor}) - 32'd1))) |=> (clkOut == 1'b0)
    );

// If clkOut is low and count matches the divisor minus one, next clkOut is high.
    check_clkout_high_when_count_matches: assert property (
        @(posedge clk) disable iff (rst)
        (!clkOut && ($signed({1'b0, count}) == ($signed({1'b0, Divisor}) - 32'd1))) |=> (clkOut == 1'b1)
    );

endmodule
