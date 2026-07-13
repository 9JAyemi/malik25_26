module updown_counter_sva (
    input logic clk,
    input logic reset,      // active-low asynchronous reset
    input logic control,    // 0: up, 1: down
    input logic [2:0] count // 3-bit counter
);
    // Reset low forces count to zero at each clock.
    reset_low_clears_count: assert property (
        @(posedge clk) (reset == 1'b0) |-> (count == 3'd0)
    );

    // Out of reset, next count matches prev control: +1 when 0, -1 when 1.
    count_update_matches_prev_control: assert property (
        @(posedge clk) disable iff (reset == 1'b0)
            $past(reset) |-> (count == ($past(control) ? ($past(count) - 3'd1) : ($past(count) + 3'd1)))
    );

    // Up-count wraps from 7 to 0 when previous control was 0.
    wrap_up_on_7_to_0: assert property (
        @(posedge clk) disable iff (reset == 1'b0)
            ($past(reset) && ($past(control) == 1'b0) && ($past(count) == 3'd7)) |-> (count == 3'd0)
    );

    // Down-count wraps from 0 to 7 when previous control was 1.
    wrap_down_on_0_to_7: assert property (
        @(posedge clk) disable iff (reset == 1'b0)
            ($past(reset) && ($past(control) == 1'b1) && ($past(count) == 3'd0)) |-> (count == 3'd7)
    );

    // Up-count increments by exactly one when not wrapping.
    increment_no_wrap: assert property (
        @(posedge clk) disable iff (reset == 1'b0)
            ($past(reset) && ($past(control) == 1'b0) && ($past(count) != 3'd7)) |-> (count == $past(count) + 3'd1)
    );

    // Down-count decrements by exactly one when not wrapping.
    decrement_no_wrap: assert property (
        @(posedge clk) disable iff (reset == 1'b0)
            ($past(reset) && ($past(control) == 1'b1) && ($past(count) != 3'd0)) |-> (count == $past(count) - 3'd1)
    );

    // While reset remains asserted across cycles, count stays at zero.
    hold_zero_during_reset: assert property (
        @(posedge clk) (!$past(reset) && !reset) |-> (count == 3'd0)
    );
endmodule