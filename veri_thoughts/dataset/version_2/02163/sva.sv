module d_ff_reset_preset_sva (
    input logic clk,
    input logic reset,   // active-low synchronous reset
    input logic preset,  // active-low synchronous preset
    input logic d,
    input logic q
);

    // q follows reset/preset/d priority on each clock edge.
    full_functional_update: assert property (
        @(posedge clk) q == (reset ? (preset ? d : 1'b1) : 1'b0)
    );

    // Active-low reset drives q to 0 on the same cycle.
    check_reset_low_forces_zero: assert property (
        @(posedge clk) !reset |-> (q == 1'b0)
    );

    // With reset high and preset low, q is set to 1.
    check_preset_low_sets_one: assert property (
        @(posedge clk) disable iff (!reset) (!preset) |-> (q == 1'b1)
    );

    // With both reset and preset high, q captures d.
    check_data_captured_when_enabled: assert property (
        @(posedge clk) disable iff (!reset) (preset) |-> (q == d)
    );

    // Reset has priority over preset when both are low.
    check_reset_priority_over_preset: assert property (
        @(posedge clk) (!reset && !preset) |-> (q == 1'b0)
    );

    // On reset falling (becoming active), q is driven to 0.
    check_fall_reset_forces_zero: assert property (
        @(posedge clk) $fell(reset) |-> (q == 1'b0)
    );

    // On preset falling (becoming active) with reset high, q is set to 1.
    check_fall_preset_sets_one: assert property (
        @(posedge clk) disable iff (!reset) $fell(preset) |-> (q == 1'b1)
    );

    // On preset rising with reset high, q is transparent to d.
    check_rise_preset_transparent: assert property (
        @(posedge clk) disable iff (!reset) $rose(preset) |-> (q == d)
    );

    // If both reset and preset are high across two cycles and d is stable, q remains stable.
    check_stable_d_implies_stable_q_when_enabled: assert property (
        @(posedge clk) disable iff (!reset)
            (preset && $past(preset) && $past(reset) && $stable(d)) |-> $stable(q)
    );

    // If both reset and preset are high across two cycles and d changes, q changes.
    check_data_change_propagates_when_enabled: assert property (
        @(posedge clk) disable iff (!reset)
            (preset && $past(preset) && $past(reset) && $changed(d)) |-> $changed(q)
    );

endmodule