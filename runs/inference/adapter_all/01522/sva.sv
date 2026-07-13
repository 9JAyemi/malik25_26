module four_bit_counter_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] count
);
    // Clock: clk (posedge). Reset: reset (active-high, asynchronous). Sequential 4-bit counter.

    // On reset deassertion, count becomes 0 on the next cycle.
    reset_deassert_sets_zero: assert property (
        @(posedge clk) disable iff (reset) $fell(reset) |-> (count == 4'd0)
    );

    // While reset is held high across cycles, count is 0.
    hold_zero_while_reset: assert property (
        @(posedge clk) (reset && $past(reset)) |-> (count == 4'd0)
    );

    // When not in reset for two consecutive cycles, count increments by 1.
    increment_when_not_reset: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset)) |-> (count == $past(count) + 4'd1)
    );

    // When not in reset for two consecutive cycles, count changes every cycle.
    change_each_cycle_when_not_reset: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset)) |-> (count != $past(count))
    );

    // When not in reset for two consecutive cycles, count wraps from 15 to 0.
    wrap_from_max: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset) && ($past(count) == 4'hF)) |-> (count == 4'h0)
    );

    // On reset assertion, count is 0 in the same cycle.
    reset_assert_sets_zero: assert property (
        @(posedge clk) reset |-> (count == 4'd0)
    );

    // On reset assertion, count remains 0 on the next cycle.
    reset_assert_next_cycle_zero: assert property (
        @(posedge clk) reset |-> ##1 (count == 4'd0)
    );

    // On reset deassertion, count is 0 in the same cycle.
    reset_deassert_sets_zero_now: assert property (
        @(posedge clk) $fell(reset) |-> (count == 4'd0)
    );

    // On reset deassertion, count is 0 on the next cycle.
    reset_deassert_next_cycle_zero: assert property (
        @(posedge clk) $fell(reset) |-> ##1 (count == 4'd0)
    );

    // If count is 0 while not in reset, the previous value was 15.
    zero_implies_prev_max: assert property (
        @(posedge clk) disable iff (reset) (count == 4'd0) |-> ($past(count) == 4'hF)
    );

    // If count is 1 while not in reset, the previous value was 0.
    one_implies_prev_zero: assert property (
        @(posedge clk) disable iff (reset) (count == 4'd1) |-> ($past(count) == 4'd0)
    );

endmodule