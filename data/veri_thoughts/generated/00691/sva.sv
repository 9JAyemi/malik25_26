module up_counter_sva (
    input logic clk,
    input logic reset,       // Active-low asynchronous reset
    input logic [2:0] count
);
    ///// Reset behavior /////
    // When reset is LOW at a clock edge, count must be 0.
    check_reset_low_forces_zero: assert property (
        @(posedge clk) (reset == 1'b0) |-> (count == 3'd0)
    );

    // On a falling edge of reset between clock edges, count must be 0 at this clock.
    check_reset_fall_clears_count: assert property (
        @(posedge clk) $fell(reset) |-> (count == 3'd0)
    );

    // While reset is held LOW across consecutive clocks, count remains 0.
    check_hold_zero_during_reset: assert property (
        @(posedge clk) (reset == 1'b0) && ($past(reset) == 1'b0) |-> (count == 3'd0)
    );

    ///// Normal counting rules (enabled when reset is HIGH) /////
    // When reset is HIGH for two consecutive clocks and prior count < 7, increment by 1.
    check_increment_when_below_max: assert property (
        @(posedge clk) disable iff (reset == 1'b0)
            ($past(reset) && reset && ($past(count) != 3'd7)) |-> (count == ($past(count) + 3'd1))
    );

    // When reset is HIGH for two consecutive clocks and prior count == 7, wrap to 0.
    check_wrap_to_zero_from_max: assert property (
        @(posedge clk) disable iff (reset == 1'b0)
            ($past(reset) && reset && ($past(count) == 3'd7)) |-> (count == 3'd0)
    );

    // With reset HIGH for two consecutive clocks, count must change every cycle (no stalls).
    check_change_each_cycle_when_enabled: assert property (
        @(posedge clk) disable iff (reset == 1'b0)
            ($past(reset) && reset) |-> (count != $past(count))
    );

    // With reset HIGH for 8 consecutive clocks, count returns to its value 8 cycles earlier.
    sequence reset_high_8;
        (reset == 1'b1) [*8];
    endsequence
    check_period_8_when_enabled: assert property (
        @(posedge clk) disable iff (reset == 1'b0)
            reset_high_8 |-> (count == $past(count, 8))
    );
endmodule