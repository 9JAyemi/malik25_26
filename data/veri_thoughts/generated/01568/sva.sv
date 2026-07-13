module counter_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] count
);
    // Clock: clk (posedge). Reset: rst (synchronous, active-high). Behavior: 4-bit up-counter with wrap at 15 to 0.

    // Reset drives count to 0 on the next cycle.
    check_reset_clears_next: assert property (
        @(posedge clk) rst |=> (count == 4'h0)
    );

    // While reset is held across cycles, count is 0.
    check_hold_zero_while_reset: assert property (
        @(posedge clk) (rst && $past(rst)) |-> (count == 4'h0)
    );

    // On reset deassertion (1->0), current cycle's count is 0.
    check_count_zero_on_reset_fall: assert property (
        @(posedge clk) $fell(rst) |-> (count == 4'h0)
    );

    // One cycle after reset deasserts, count becomes 1.
    check_count_one_after_reset_release: assert property (
        @(posedge clk) $fell(rst) |=> (count == 4'd1)
    );

    // If previous cycle was not in reset and count was not max, it increments by 1.
    check_increment_when_prev_not_max: assert property (
        @(posedge clk) disable iff (rst) (!$past(rst) && ($past(count) != 4'hF)) |-> (count == ($past(count) + 4'd1))
    );

    // If previous cycle was not in reset and count was max, it wraps to 0.
    check_wrap_when_prev_max: assert property (
        @(posedge clk) disable iff (rst) (!$past(rst) && ($past(count) == 4'hF)) |-> (count == 4'h0)
    );

    // If previous cycle was not in reset and not max, next value is not 0.
    check_no_spurious_zero_when_prev_not_max: assert property (
        @(posedge clk) disable iff (rst) (!$past(rst) && ($past(count) != 4'hF)) |-> (count != 4'h0)
    );

endmodule