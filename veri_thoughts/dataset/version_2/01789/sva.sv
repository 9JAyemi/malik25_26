module counter_sva (
    input logic clk,
    input logic reset,      // Active-high synchronous reset
    input logic [3:0] count // 4-bit up-counter output
);

    // If reset was asserted in the previous cycle, count is 0 now.
    check_reset_clears_count: assert property (
        @(posedge clk) disable iff (reset)
            $past(reset) |-> (count == 4'd0)
    );

    // If last cycle was not reset and not at max, increment by 1.
    check_increment_nonwrap: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset) && ($past(count) != 4'hF)) |-> (count == $past(count) + 4'd1)
    );

    // If last cycle was not reset and at max, wrap to 0.
    check_wrap_on_max: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset) && ($past(count) == 4'hF)) |-> (count == 4'd0)
    );

    // Without reset last cycle, count must change every cycle.
    check_change_each_cycle_without_reset: assert property (
        @(posedge clk) disable iff (reset)
            !$past(reset) |-> (count != $past(count))
    );

    // Over two cycles without reset and starting <=13, net increment is +2.
    check_two_cycle_increment_small_range: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset,2) && !$past(reset,1) && ($past(count,2) <= 4'd13)) |-> (count == $past(count,2) + 4'd2)
    );

    // Over two cycles without reset, starting at 14 wraps to 0.
    check_two_cycle_wrap_from_14: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset,2) && !$past(reset,1) && ($past(count,2) == 4'd14)) |-> (count == 4'd0)
    );

    // Over two cycles without reset, starting at 15 ends at 1.
    check_two_cycle_wrap_from_15: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset,2) && !$past(reset,1) && ($past(count,2) == 4'd15)) |-> (count == 4'd1)
    );

    // With no resets for 16 cycles, the count value repeats.
    check_16_cycle_periodicity_no_reset: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset,1)  && !$past(reset,2)  && !$past(reset,3)  && !$past(reset,4)  &&
             !$past(reset,5)  && !$past(reset,6)  && !$past(reset,7)  && !$past(reset,8)  &&
             !$past(reset,9)  && !$past(reset,10) && !$past(reset,11) && !$past(reset,12) &&
             !$past(reset,13) && !$past(reset,14) && !$past(reset,15) && !$past(reset,16))
            |-> (count == $past(count,16))
    );

    // If last cycle was not reset and count is 0 now, previous count was 15.
    check_zero_implies_prev_15_when_no_prev_reset: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset) && (count == 4'd0)) |-> ($past(count) == 4'hF)
    );

    // Over three cycles without reset and starting <=12, net increment is +3.
    check_three_cycle_increment_small_range: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset,3) && !$past(reset,2) && !$past(reset,1) && ($past(count,3) <= 4'd12)) |-> (count == $past(count,3) + 4'd3)
    );

endmodule