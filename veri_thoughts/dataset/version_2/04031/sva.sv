module pwm_fade_sva #(
    parameter int LEVEL_BITS = 8,
    parameter int FADE_BITS  = 26
) (
    input logic clk,
    input logic trigger,
    input logic drive,
    input logic [LEVEL_BITS-1:0] pwm_counter,
    input logic [FADE_BITS-1:0]  fade_counter,
    input logic [LEVEL_BITS-1:0] level
);

    // PWM counter increments by one every clock.
    check_pwm_counter_increments: assert property (
        @(posedge clk) 1'b1 |=> (pwm_counter == ($past(pwm_counter) + 1'b1))
    );

    // Trigger reloads the fade counter to all ones.
    check_trigger_loads_fade_max: assert property (
        @(posedge clk) trigger |=> (fade_counter == {FADE_BITS{1'b1}})
    );

    // Nonzero fade counter decrements by one when trigger is low.
    check_fade_counter_decrements_without_trigger: assert property (
        @(posedge clk) (!trigger && (|fade_counter)) |=> (fade_counter == ($past(fade_counter) - 1'b1))
    );

    // Zero fade counter stays at zero when trigger is low.
    check_fade_counter_holds_zero_without_trigger: assert property (
        @(posedge clk) (!trigger && (fade_counter == {FADE_BITS{1'b0}})) |=> (fade_counter == {FADE_BITS{1'b0}})
    );

    // Level is always the top LEVEL_BITS of the fade counter.
    check_level_matches_fade_counter_msbs: assert property (
        @(posedge clk) (level == fade_counter[FADE_BITS-1 -: LEVEL_BITS])
    );

    // Drive matches the PWM compare against level.
    check_drive_matches_pwm_compare: assert property (
        @(posedge clk) (drive == (pwm_counter < level))
    );

    // Trigger produces a full-scale level on the next cycle.
    check_trigger_sets_full_level: assert property (
        @(posedge clk) trigger |=> (level == {LEVEL_BITS{1'b1}})
    );

    // Zero fade counter implies zero level.
    check_zero_fade_forces_zero_level: assert property (
        @(posedge clk) (fade_counter == {FADE_BITS{1'b0}}) |-> (level == {LEVEL_BITS{1'b0}})
    );

    // Zero fade counter forces drive low.
    check_zero_fade_forces_drive_low: assert property (
        @(posedge clk) (fade_counter == {FADE_BITS{1'b0}}) |-> (!drive)
    );

endmodule