module sync_counter_sva (
    input logic clk,
    input logic reset,       // active-high synchronous reset
    input logic enable,
    input logic direction,
    input logic [3:0] count
);

    // Reset drives count to zero on the next clock.
    reset_clears_next: assert property (
        @(posedge clk) reset |=> (count == 4'b0000)
    );

    // If reset is held across consecutive cycles, count is zero in the later cycle.
    reset_held_forces_zero: assert property (
        @(posedge clk) ($past(reset) && reset) |-> (count == 4'b0000)
    );

    // With enable LOW (and no reset), count holds its value to the next cycle.
    hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset) (!enable) |=> (count == $past(count))
    );

    // With enable HIGH and direction LOW, count increments by 1 with wrap at 4'hF->4'h0.
    increment_with_wrap: assert property (
        @(posedge clk) disable iff (reset)
        (enable && !direction) |=> (
            ($past(count) == 4'hF) ? (count == 4'h0) : (count == $past(count) + 4'd1)
        )
    );

    // With enable HIGH and direction HIGH, count decrements by 1 with wrap at 4'h0->4'hF.
    decrement_with_wrap: assert property (
        @(posedge clk) disable iff (reset)
        (enable && direction) |=> (
            ($past(count) == 4'h0) ? (count == 4'hF) : (count == $past(count) - 4'd1)
        )
    );

    // When enable is HIGH (and no reset), count must change on the next cycle.
    enabled_changes_count: assert property (
        @(posedge clk) disable iff (reset) enable |=> (count != $past(count))
    );

    // Any change in count must be due to reset or enable being HIGH in the prior cycle.
    change_requires_enable_or_reset: assert property (
        @(posedge clk) (count != $past(count)) |-> ($past(reset) || $past(enable))
    );

    // Increment wrap: at max (4'hF) with increment command, next count is 4'h0.
    increment_wrap_from_max: assert property (
        @(posedge clk) disable iff (reset)
        (enable && !direction && ($past(count) == 4'hF)) |=> (count == 4'h0)
    );

    // Decrement wrap: at min (4'h0) with decrement command, next count is 4'hF.
    decrement_wrap_from_min: assert property (
        @(posedge clk) disable iff (reset)
        (enable && direction && ($past(count) == 4'h0)) |=> (count == 4'hF)
    );

    // If neither reset nor enable were asserted in the prior cycle, count must not change.
    no_change_without_enable_or_reset_prev: assert property (
        @(posedge clk) (!$past(reset) && !$past(enable)) |-> (count == $past(count))
    );

endmodule