module binary_counter_sva (
    input logic clk,
    input logic [3:0] reset,
    input logic [3:0] enable,
    input logic [3:0] count
);
    // Clock: clk (posedge). Reset: reset (synchronous, active-high). Sequential counter with enable.

    // Reset drives count to zero on the next cycle.
    reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 4'b0000)
    );

    // When enabled without reset, count increments by 1 (mod 16).
    count_increments_when_enabled: assert property (
        @(posedge clk) disable iff (reset) enable |=> (count == $past(count) + 4'd1)
    );

    // When not enabled without reset, count holds its value.
    count_holds_when_disabled: assert property (
        @(posedge clk) disable iff (reset) !enable |=> (count == $past(count))
    );

    // Any change in count must be caused by reset or enable in the prior cycle.
    count_change_requires_enable_or_reset: assert property (
        @(posedge clk) disable iff (reset) (count != $past(count)) |-> ($past(reset) || $past(enable))
    );

    // If reset and enable are both high, reset has priority and count becomes zero next cycle.
    reset_priority_over_enable: assert property (
        @(posedge clk) (reset && enable) |=> (count == 4'b0000)
    );

    // If count is zero without reset, it must be due to reset or wrap from 15 when enabled.
    zero_count_cause: assert property (
        @(posedge clk) disable iff (reset) (count == 4'b0000) |-> ($past(reset) || ($past(enable) && ($past(count) == 4'hF)))
    );

    // If count is 15 and enabled without reset, it wraps to 0 on the next cycle.
    wrap_from_max_when_enabled: assert property (
        @(posedge clk) disable iff (reset) (enable && (count == 4'hF)) |=> (count == 4'h0)
    );

    // If count is 15 and not enabled without reset, it stays at 15.
    hold_at_max_when_disabled: assert property (
        @(posedge clk) disable iff (reset) (!enable && (count == 4'hF)) |=> (count == 4'hF)
    );

    // If count is 0 and not reset, it must be due to wrap from 15 when enabled previously.
    zero_without_reset_implies_prev_wrap: assert property (
        @(posedge clk) disable iff (reset) (count == 4'h0) |-> ($past(reset) || ($past(enable) && ($past(count) == 4'hF)))
    );

    // If count changes, the new value must differ from the previous value.
    count_change_is_nonzero: assert property (
        @(posedge clk) disable iff (reset) (count != $past(count)) |-> (count != $past(count,1))
    );
endmodule