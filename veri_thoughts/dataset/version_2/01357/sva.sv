module counter_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [15:0] count
);

    // When reset is asserted, count must be zero on that cycle.
    reset_clears_count: assert property (
        @(posedge clk) reset |-> (count == 16'd0)
    );

    // With enable and no reset, count increments by 1 from previous value.
    inc_on_enable: assert property (
        @(posedge clk) disable iff (reset) enable |-> (count == $past(count) + 16'd1)
    );

    // With !enable and no reset, count holds its previous value.
    hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset) !enable |-> (count == $past(count))
    );

    // Without reset, any change to count must be due to enable.
    change_requires_enable: assert property (
        @(posedge clk) disable iff (reset) $changed(count) |-> enable
    );

    // Wrap-around when previous value was 0xFFFF and enable is asserted.
    wrap_on_max: assert property (
        @(posedge clk) disable iff (reset) (enable && ($past(count) == 16'hFFFF)) |-> (count == 16'h0000)
    );

    // If enable stays high for two cycles with no reset in those cycles, count increases by 2.
    two_cycle_inc_streak: assert property (
        @(posedge clk) disable iff (reset)
            (enable && $past(enable) && !$past(reset) && !$past($past(reset)))
            |-> (count == $past($past(count)) + 16'd2)
    );

    // If enable stays low for two cycles with no reset in those cycles, count is unchanged across two cycles.
    two_cycle_hold_streak: assert property (
        @(posedge clk) disable iff (reset)
            (!enable && !$past(enable) && !$past(reset) && !$past($past(reset)))
            |-> (count == $past($past(count)))
    );

    // Reset dominates enable when both are asserted.
    reset_dominates_enable: assert property (
        @(posedge clk) (reset && enable) |-> (count == 16'd0)
    );

endmodule