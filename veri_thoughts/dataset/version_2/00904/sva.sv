module synchronous_counter_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] count
);
    ///// Reset behavior /////
    // While reset is HIGH at a clock edge, count must be 0.
    check_reset_forces_zero: assert property (
        @(posedge clk) reset |-> (count == 4'd0)
    );

    ///// Normal counting behavior (when not in reset) /////
    // If last cycle was not reset and count <= 8, increment by 1.
    check_increment_when_below_9: assert property (
        @(posedge clk) disable iff (reset)
            (!$initstate && $past(!reset) && ($past(count) <= 4'd8)) |-> (count == $past(count) + 4'd1)
    );

    // If last cycle was not reset and count was 9, wrap to 0.
    check_wrap_from_9_to_0: assert property (
        @(posedge clk) disable iff (reset)
            (!$initstate && $past(!reset) && ($past(count) == 4'd9)) |-> (count == 4'd0)
    );

    // After at least one non-reset cycle, count must be within 0..9.
    check_range_after_nonreset: assert property (
        @(posedge clk) disable iff (reset)
            (!$initstate && $past(!reset)) |-> (count <= 4'd9)
    );

    // If not in reset now and previously not in reset, a zero must come from a wrap from 9.
    check_zero_only_from_wrap_no_reset: assert property (
        @(posedge clk) disable iff (reset)
            (!$initstate && !reset && $past(!reset) && (count == 4'd0)) |-> ($past(count) == 4'd9)
    );

    // If last cycle was not reset and count <= 8, the value must change (no hold).
    check_no_hold_when_below_9: assert property (
        @(posedge clk) disable iff (reset)
            (!$initstate && $past(!reset) && ($past(count) <= 4'd8)) |-> (count != $past(count))
    );

    ///// Reset release behavior /////
    // On reset falling edge, count is 0 this cycle and 1 on the next (if reset stays low).
    check_post_reset_first_increment: assert property (
        @(posedge clk) disable iff (reset)
            $fell(reset) |-> (count == 4'd0) ##1 (count == 4'd1)
    );

    ///// Periodicity /////
    // With no reset for 10 cycles, count repeats every 10 cycles.
    check_period_10_no_reset: assert property (
        @(posedge clk) disable iff (reset)
            1'b1 |-> ##10 (count == $past(count, 10))
    );
endmodule