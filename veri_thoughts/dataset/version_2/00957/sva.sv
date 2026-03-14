module binary_counter_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] count
);
    // On the previous cycle without reset, count increments by 1.
    check_increment_on_prev_no_reset: assert property (
        @(posedge clk) disable iff (rst)
            $past(!rst) |-> (count == $past(count) + 4'd1)
    );

    // From 4'hF, next value wraps to 4'h0 when not in reset.
    check_wrap_from_max: assert property (
        @(posedge clk) disable iff (rst)
            $past(!rst) && ($past(count) == 4'hF) |-> (count == 4'h0)
    );

    // When not in reset previously, count must change every cycle.
    check_change_each_cycle_no_reset: assert property (
        @(posedge clk) disable iff (rst)
            $past(!rst) |-> (count != $past(count))
    );

    // Asserting reset drives count to 0 on the next clock.
    check_reset_clears_next_cycle: assert property (
        @(posedge clk) rst |-> ##1 (count == 4'd0)
    );

    // If reset is high two cycles in a row, current count is 0.
    check_held_reset_forces_zero: assert property (
        @(posedge clk) $past(rst) && rst |-> (count == 4'd0)
    );

    // Immediately after reset deasserts, count is still 0.
    check_deassertion_leaves_zero_now: assert property (
        @(posedge clk) $past(rst) && !rst |-> (count == 4'd0)
    );

    // Two consecutive non-reset cycles increase count by 2.
    check_two_cycle_increment: assert property (
        @(posedge clk) disable iff (rst)
            $past(!rst,2) && $past(!rst,1) |-> (count == $past(count,2) + 4'd2)
    );
endmodule