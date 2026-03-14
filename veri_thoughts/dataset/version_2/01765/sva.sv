module counter_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] count
);
    // Next state equals 0 after a prior reset, else prior value + 1 (mod 16).
    check_next_state_function: assert property (
        @(posedge clk) !$initstate |-> (count == ($past(reset) ? 4'd0 : (($past(count) + 4'd1) & 4'hF)))
    );

    // Without prior reset, count increments by exactly 1 (mod 16).
    check_increment_no_reset: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset)) |-> (count == (($past(count) + 4'd1) & 4'hF))
    );

    // After a reset cycle, count is 0 on the following cycle.
    check_zero_after_reset_cycle: assert property (
        @(posedge clk) $past(reset) |-> (count == 4'd0)
    );

    // If reset is asserted in two consecutive cycles, count is 0 on the second.
    check_zero_while_reset: assert property (
        @(posedge clk) (reset && $past(reset)) |-> (count == 4'd0)
    );

    // If last cycle was not reset and count was 15, it wraps to 0.
    check_wraparound_from_F_to_0: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset) && ($past(count) == 4'hF)) |-> (count == 4'd0)
    );

    // While reset is held across clock edges, count remains stable.
    check_stable_during_continuous_reset: assert property (
        @(posedge clk) (reset && $past(reset)) |-> $stable(count)
    );
endmodule