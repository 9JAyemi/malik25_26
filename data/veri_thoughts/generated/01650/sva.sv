module up_counter_sva (
    input logic clk,
    input logic reset,   // active-high synchronous reset
    input logic enable,
    input logic [2:0] count
);

    ///// Reset behavior /////
    // When reset is asserted, count is driven to 0 on that clock.
    reset_forces_zero: assert property (
        @(posedge clk) reset |-> (count == 3'b000)
    );

    ///// Increment and hold behavior /////
    // When enabled (and not in reset), count increments by 1.
    increment_on_enable: assert property (
        @(posedge clk) disable iff (reset) (!$initstate && enable) |-> (count == $past(count) + 3'd1)
    );

    // When not enabled (and not in reset), count holds its value.
    hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset) (!$initstate && !enable) |-> (count == $past(count))
    );

    // Any change to count (out of reset) must be due to enable being 1.
    change_only_with_enable: assert property (
        @(posedge clk) disable iff (reset) (!$initstate && (count != $past(count))) |-> enable
    );

    // Explicit wrap-around: from 7 to 0 when enabled (out of reset).
    wrap_7_to_0: assert property (
        @(posedge clk) disable iff (reset) (!$initstate && enable && ($past(count) == 3'd7)) |-> (count == 3'd0)
    );

    ///// Behavior immediately after leaving reset /////
    // If reset deasserts and enable is 0, count remains 0.
    hold_zero_after_reset_if_disabled: assert property (
        @(posedge clk) $fell(reset) && !enable |-> (count == 3'd0)
    );

    // If reset deasserts and enable is 1, count becomes 1.
    increment_from_zero_after_reset_if_enabled: assert property (
        @(posedge clk) $fell(reset) && enable |-> (count == 3'd1)
    );

endmodule