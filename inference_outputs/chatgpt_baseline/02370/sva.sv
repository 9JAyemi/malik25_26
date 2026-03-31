module counter_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [3:0] count,
    input logic overflow
);
    // Clock: posedge clk; Reset: active-high synchronous 'reset'; Logic: sequential.

    // Synchronous reset drives count=0 and overflow=0 on the following cycle.
    reset_clears_outputs_next: assert property (
        @(posedge clk) reset |=> (count == 4'h0) && (overflow == 1'b0)
    );

    // When disabled, both outputs hold their previous values.
    hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset) (!enable) |=> (count == $past(count)) && (overflow == $past(overflow))
    );

    // With enable and count==15, next count wraps to 0 and overflow asserts.
    wrap_sets_overflow_and_zero: assert property (
        @(posedge clk) disable iff (reset) (enable && (count == 4'hF)) |=> (count == 4'h0) && (overflow == 1'b1)
    );

    // With enable and count!=15, next count increments by 1.
    increment_when_enabled: assert property (
        @(posedge clk) disable iff (reset) (enable && (count != 4'hF)) |=> (count == $past(count) + 4'd1)
    );

    // With enable and count!=15, next overflow is 0.
    no_overflow_on_non_wrap: assert property (
        @(posedge clk) disable iff (reset) (enable && (count != 4'hF)) |=> (overflow == 1'b0)
    );

    // Overflow high implies count is 0 in the same cycle.
    overflow_implies_count_zero_current: assert property (
        @(posedge clk) disable iff (reset) overflow |-> (count == 4'h0)
    );

    // When enabled, count must change on the next cycle.
    count_changes_when_enabled: assert property (
        @(posedge clk) disable iff (reset) enable |=> (count != $past(count))
    );

    // Outputs change only if previous cycle had reset or enable asserted.
    outputs_change_only_due_to_enable_or_reset: assert property (
        @(posedge clk) disable iff (reset)
            ((count != $past(count)) || (overflow != $past(overflow)))
            |-> ($past(reset) || $past(enable))
    );

    // Overflow 0->1 transition occurs only after a wrapped increment (prev enable && prev count==15).
    overflow_rise_corresponds_to_wrap: assert property (
        @(posedge clk) disable iff (reset)
            $rose(overflow) |-> ($past(!reset) && $past(enable) && ($past(count) == 4'hF))
    );

endmodule