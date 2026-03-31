module binary_counter_sva (
    input logic clk,
    input logic EN,
    input logic RST,
    input logic [3:0] COUNT
);

    ///// Reset behavior /////
    // When reset is asserted (active-low), COUNT is 0 in the same cycle.
    reset_level_forces_zero: assert property (
        @(posedge clk) (RST == 1'b0) |-> (COUNT == 4'b0000)
    );

    // If reset was asserted in the previous cycle, COUNT is 0 now.
    reset_previous_cycle_low_forces_zero: assert property (
        @(posedge clk) ($past(RST) == 1'b0) |-> (COUNT == 4'b0000)
    );

    // If reset is held low across consecutive cycles, COUNT stays at 0.
    reset_held_low_keeps_zero_stable: assert property (
        @(posedge clk) ((RST == 1'b0) && ($past(RST) == 1'b0)) |-> (COUNT == 4'b0000) && $stable(COUNT)
    );

    // On a sampled falling edge of reset, COUNT is 0.
    reset_fall_sampled_forces_zero: assert property (
        @(posedge clk) $fell(RST) |-> (COUNT == 4'b0000)
    );

    // On a sampled rising edge of reset (previous cycle in reset), COUNT is 0.
    reset_rise_sampled_shows_zero: assert property (
        @(posedge clk) $rose(RST) |-> (COUNT == 4'b0000)
    );

    // Reset has priority over enable; if both active, COUNT is 0.
    reset_priority_over_enable: assert property (
        @(posedge clk) (RST == 1'b0 && EN == 1'b1) |-> (COUNT == 4'b0000)
    );

    // COUNT must be known while reset is asserted.
    no_x_during_reset: assert property (
        @(posedge clk) (RST == 1'b0) |-> (!$isunknown(COUNT))
    );

endmodule