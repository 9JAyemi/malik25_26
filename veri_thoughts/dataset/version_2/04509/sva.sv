module up_counter_sva (
    input logic       clk,
    input logic       reset,
    input logic [3:0] count_out
);

    // A sampled reset assertion clears count_out by the next clock.
    reset_rise_clears_count_by_next_clk: assert property (
        @(posedge clk) disable iff ($initstate)
        $rose(reset) |=> (count_out == 4'b0000)
    );

    // While reset stays asserted across sampled clocks, count_out stays zero.
    reset_held_high_keeps_count_zero: assert property (
        @(posedge clk) disable iff ($initstate)
        (reset && $past(reset)) |-> (count_out == 4'b0000)
    );

    // On the sampled reset release edge, count_out is still zero.
    reset_fall_starts_from_zero: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        $fell(reset) |-> (count_out == 4'b0000)
    );

    // After reset release, count_out never exceeds one until reset is asserted again.
    post_reset_count_bounded: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        $fell(reset) |=> (count_out <= 4'd1)[*1:$]
    );

    // Each sampled transition is a hold, a +1 increment, or a move to zero.
    count_transition_is_hold_increment_or_zero: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        (count_out == 4'b0000) ||
        (count_out == $past(count_out)) ||
        (count_out == ($past(count_out) + 4'b0001))
    );

    // Any sampled change to a nonzero count_out value is a +1 increment.
    nonzero_count_change_is_increment: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        ($changed(count_out) && (count_out != 4'b0000)) |-> (count_out == ($past(count_out) + 4'b0001))
    );

    // After a nonzero increment is observed, the next sampled value holds or returns to zero.
    nonzero_increment_then_hold_or_zero: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        ($changed(count_out) && (count_out != 4'b0000)) |=> ((count_out == $past(count_out)) || (count_out == 4'b0000))
    );

endmodule