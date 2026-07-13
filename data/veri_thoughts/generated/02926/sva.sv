module binary_counter_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] count
);
    ///// Reset behavior /////
    // While reset is HIGH on a clock edge, count is 0.
    reset_clears_count: assert property (
        @(posedge clk) reset |-> (count == 4'd0)
    );

    // If reset stays HIGH across consecutive cycles, count remains 0.
    zero_held_during_continuous_reset: assert property (
        @(posedge clk) reset && $past(reset) |-> (count == 4'd0) && ($past(count) == 4'd0)
    );

    ///// Counting behavior /////
    // When not in reset in back-to-back cycles, count increments by 1.
    inc_when_prev_not_reset: assert property (
        @(posedge clk) disable iff (reset) !$past(reset) |-> (count == $past(count) + 4'd1)
    );

    // On the first cycle after reset deasserts, count becomes 1.
    inc_after_reset_release_is_one: assert property (
        @(posedge clk) disable iff (reset) $past(reset) && !reset |-> (count == 4'd1)
    );

    // When running, count does not hold its previous value.
    no_stall_when_running: assert property (
        @(posedge clk) disable iff (reset) !$past(reset) |-> (count != $past(count))
    );

    // When running and previous count was 15, next count wraps to 0.
    wrap_on_max: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset) && ($past(count) == 4'd15)) |-> (count == 4'd0)
    );

    // When running for two consecutive prior cycles, count advances by 2 over two cycles.
    two_cycle_inc_when_running: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset) && !$past(reset,2)) |-> (count == $past(count,2) + 4'd2)
    );

    // When running and previous count was not 15, next count is not 0.
    nonzero_when_prev_not15: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset) && ($past(count) != 4'd15)) |-> (count != 4'd0)
    );
endmodule