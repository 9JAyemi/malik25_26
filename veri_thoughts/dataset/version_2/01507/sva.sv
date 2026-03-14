module up_counter_3bit_sva (
    input logic clk,
    input logic reset,
    input logic [2:0] count
);

    // If reset is asserted on this clock, count is 0 on the next clock.
    check_sync_reset_clears_next: assert property (
        @(posedge clk) reset |=> (count == 3'd0)
    );

    // If reset was asserted in the previous cycle, count must be 0 now.
    check_prev_reset_zero_now: assert property (
        @(posedge clk) $past(reset) |-> (count == 3'd0)
    );

    // When not in reset in the previous cycle, count increments by 1 modulo 8.
    check_increment_when_prev_not_reset: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) |-> (count == ($past(count) + 3'd1))
    );

    // Explicit wraparound: from 7 to 0 when previous cycle was not in reset.
    check_wrap_7_to_0: assert property (
        @(posedge clk) disable iff (reset) ($past(!reset) && ($past(count) == 3'd7)) |-> (count == 3'd0)
    );

    // While reset is held across consecutive cycles, count stays at 0.
    check_hold_zero_during_reset: assert property (
        @(posedge clk) (reset && $past(reset)) |-> (count == 3'd0)
    );

    // First value after reset release is 1 (incrementing from 0 assigned during reset).
    check_first_value_after_reset_release: assert property (
        @(posedge clk) (!reset && $past(reset)) |=> (count == 3'd1)
    );

endmodule