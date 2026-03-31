module ClockDivider_sva (
    input logic [31:0] Divisor,
    input logic clkOut,
    input logic clk,
    input logic rst
);

// Reset drives clkOut low on the next clock.
    check_reset_clears_clkout: assert property (
        @(posedge clk) rst |=> (clkOut == 1'b0)
    );

// clkOut is low when reset is asserted.
    check_clkout_low_during_reset: assert property (
        @(posedge clk) rst |-> (clkOut == 1'b0)
    );

// clkOut is high when not in reset and the counter is not at the threshold.
    check_clkout_high_when_not_threshold: assert property (
        @(posedge clk) disable iff (rst)
        ($signed({1'b0, count_i}) != $signed({1'b0, Divisor}) - 1) |-> (clkOut == 1'b1)
    );

// clkOut is low when not in reset and the counter is at the threshold.
    check_clkout_low_when_threshold: assert property (
        @(posedge clk) disable iff (rst)
        ($signed({1'b0, count_i}) == $signed({1'b0, Divisor}) - 1) |-> (clkOut == 1'b0)
    );

endmodule
