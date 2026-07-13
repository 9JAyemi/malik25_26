module ClockDivider_sva (
    input logic [31:0] Divisor,
    input logic        clkOut,
    input logic        clk,
    input logic        rst,
    input logic [31:0] count_i,
    input logic        clkOut_i
);

    // clkOut continuously reflects clkOut_i.
    check_clkout_matches_internal: assert property (
        @(posedge clk) disable iff (rst)
        clkOut == clkOut_i
    );

    // Counter is zero on the first sampled cycle after reset is released.
    check_count_zero_after_reset_release: assert property (
        @(posedge clk) disable iff (rst)
        $fell(rst) |-> (count_i == 32'd0)
    );

    // Output register is low on the first sampled cycle after reset is released.
    check_clkout_reg_low_after_reset_release: assert property (
        @(posedge clk) disable iff (rst)
        $fell(rst) |-> (clkOut_i == 1'b0)
    );

    // Reaching Divisor-1 wraps the counter to zero on the next cycle.
    check_count_wraps_at_terminal_count: assert property (
        @(posedge clk) disable iff (rst)
        ($signed({1'b0, count_i}) == ($signed({1'b0, Divisor}) - 1)) |=> (count_i == 32'd0)
    );

    // Before the terminal count, the counter increments by one each cycle.
    check_count_increments_when_not_terminal: assert property (
        @(posedge clk) disable iff (rst)
        !($signed({1'b0, count_i}) == ($signed({1'b0, Divisor}) - 1)) |=> (count_i == ($past(count_i) + 32'd1))
    );

    // Reaching Divisor-1 toggles the internal output register on the next cycle.
    check_clkout_reg_toggles_at_terminal_count: assert property (
        @(posedge clk) disable iff (rst)
        ($signed({1'b0, count_i}) == ($signed({1'b0, Divisor}) - 1)) |=> (clkOut_i == ~$past(clkOut_i))
    );

    // Before the terminal count, the internal output register holds its value.
    check_clkout_reg_holds_when_not_terminal: assert property (
        @(posedge clk) disable iff (rst)
        !($signed({1'b0, count_i}) == ($signed({1'b0, Divisor}) - 1)) |=> (clkOut_i == $past(clkOut_i))
    );

endmodule