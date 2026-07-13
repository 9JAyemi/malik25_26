module counter_sva (
    input logic CLK,
    input logic reset,
    input logic enable,
    input logic [3:0] count
);
    // Clock: CLK (posedge). Reset: reset (synchronous, active-high). Sequential counter with enable.

    // Reset drives count to zero on the next cycle.
    reset_clears_next: assert property (
        @(posedge CLK) reset |=> (count == 4'b0000)
    );

    // When enabled and not in reset, count increments by 1 on the next cycle.
    increment_when_enabled: assert property (
        @(posedge CLK) disable iff (reset) enable |=> (count == $past(count) + 4'd1)
    );

    // When not enabled and not in reset, count holds its value on the next cycle.
    hold_when_disabled: assert property (
        @(posedge CLK) disable iff (reset) !enable |=> (count == $past(count))
    );

    // Any change in count (excluding reset) requires enable to be high.
    change_requires_enable: assert property (
        @(posedge CLK) disable iff (reset) (count != $past(count)) |-> $past(enable)
    );

    // If count is zero and not in reset, the previous cycle must have been a reset or a disabled cycle.
    zero_implies_prev_reset_or_hold: assert property (
        @(posedge CLK) disable iff (reset) (count == 4'b0000) |-> ($past(reset) || !$past(enable))
    );

    // If count is 15 and not in reset, the previous cycle must have been a reset or an enabled cycle.
    max_implies_prev_reset_or_enable: assert property (
        @(posedge CLK) disable iff (reset) (count == 4'hF) |-> ($past(reset) || $past(enable))
    );

    // If previous cycle was not reset and not enabled, count must be unchanged.
    no_change_when_prev_disabled: assert property (
        @(posedge CLK) disable iff (reset) (!$past(reset) && !$past(enable)) |-> (count == $past(count))
    );

    // If previous cycle was not reset and enabled, count must be incremented by 1.
    increment_when_prev_enabled: assert property (
        @(posedge CLK) disable iff (reset) (!$past(reset) && $past(enable)) |-> (count == $past(count) + 4'd1)
    );

    // If previous cycle was reset, count must be zero now.
    zero_after_prev_reset: assert property (
        @(posedge CLK) disable iff (reset) $past(reset) |-> (count == 4'b0000)
    );

    // If previous cycle was enabled and not reset, count must be non-zero now.
    non_zero_after_prev_enable: assert property (
        @(posedge CLK) disable iff (reset) (!$past(reset) && $past(enable)) |-> (count != 4'b0000)
    );

endmodule