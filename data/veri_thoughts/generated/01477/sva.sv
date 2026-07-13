module binary_counter_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [3:0] count
);

    // Reset high drives count to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |-> (count == 4'h0)
    );

    // With enable low, count holds its previous value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset) (!enable) |-> (count == $past(count))
    );

    // With enable high and below max, count increments by 1.
    check_increment_when_enabled_not_max: assert property (
        @(posedge clk) disable iff (reset) (enable && ($past(count) != 4'hF)) |-> (count == $past(count) + 1)
    );

    // With enable high at max, count wraps to zero.
    check_wrap_to_zero_when_enabled_at_max: assert property (
        @(posedge clk) disable iff (reset) (enable && ($past(count) == 4'hF)) |-> (count == 4'h0)
    );

    // Any change in count requires enable high.
    check_change_requires_enable: assert property (
        @(posedge clk) disable iff (reset) (count != $past(count)) |-> enable
    );

    // If count increments by 1, enable must be high.
    check_increment_implies_enable: assert property (
        @(posedge clk) disable iff (reset) (count == ($past(count) + 1)) |-> enable
    );

    // A decrease across cycles can only be wrap 15->0.
    check_decrease_only_on_wrap: assert property (
        @(posedge clk) disable iff (reset) (count < $past(count)) |-> (($past(count) == 4'hF) && (count == 4'h0))
    );

    // A 15->0 wrap requires enable high.
    check_wrap_transition_requires_enable: assert property (
        @(posedge clk) disable iff (reset) (($past(count) == 4'hF) && (count == 4'h0)) |-> enable
    );

    // With enable high and count is zero, previous must be 15 (not due to reset).
    check_zero_with_enable_prev_max: assert property (
        @(posedge clk) disable iff (reset) (enable && (count == 4'h0) && $past(1'b1)) |-> ($past(count) == 4'hF)
    );

    // With enable low and previous 15, count stays 15.
    check_max_holds_when_disabled: assert property (
        @(posedge clk) disable iff (reset) (($past(count) == 4'hF) && !enable) |-> (count == 4'hF)
    );

endmodule