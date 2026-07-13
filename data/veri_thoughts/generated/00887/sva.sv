module counter_sva (
    input  logic        clk,
    input  logic        reset,   // active-high synchronous reset
    input  logic [3:0]  count
);

    ///// Reset behavior /////
    // When reset is asserted, count must be 0 in that cycle.
    check_reset_forces_zero: assert property (
        @(posedge clk) reset |-> (count == 4'd0)
    );

    // While reset is held across consecutive cycles, count remains stable (stays 0).
    check_stable_during_held_reset: assert property (
        @(posedge clk) reset && $past(reset) |-> $stable(count)
    );

    ///// Counting behavior out of reset /////
    // When not in reset, count increments by 1 modulo 16 each cycle.
    check_increment_out_of_reset: assert property (
        @(posedge clk) disable iff (reset) count == ( ($past(count) + 5'd1) & 5'h0F )
    );

    // On reset deassertion (1->0), the first value becomes 1 (since previous cycle was 0).
    check_first_value_after_reset: assert property (
        @(posedge clk) $fell(reset) |-> (count == 4'd1)
    );

    // If previous count was 15 and reset stays deasserted, wrap to 0 next cycle.
    check_wrap_from_f_to_0_without_reset: assert property (
        @(posedge clk) (!$past(reset) && !reset && ($past(count) == 4'hF)) |-> (count == 4'd0)
    );

    // If not wrapping (prev != 15) and not in reset, next value cannot be 0.
    check_no_unexpected_zero_out_of_reset: assert property (
        @(posedge clk) (!reset && !$past(reset) && ($past(count) != 4'hF)) |-> (count != 4'd0)
    );

endmodule