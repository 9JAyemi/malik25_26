module pwm_fade_sva #(
    parameter int LEVEL_BITS = 8,
    parameter int FADE_BITS  = 27
) (
    // DUT ports
    input  logic                       clk,
    input  logic                       trigger,
    input  logic                       drive,
    // Internal DUT signals (bind these from the instance)
    input  logic [LEVEL_BITS-1:0]      pwm_counter,
    input  logic [FADE_BITS-1:0]       fade_counter,
    input  logic [LEVEL_BITS-1:0]      level
);
    // Clock: clk; no reset present in RTL.
    // Logic: mixed (sequential counters, combinational compare/slice).
    // Behavior: pwm_counter++ each clk; trigger reloads fade_counter to all 1s, else it counts down to 0; level = MSBs of fade_counter; drive = (pwm_counter < level).

    localparam logic [FADE_BITS-1:0]  FADE_ALL_ONES = {FADE_BITS{1'b1}};
    localparam logic [LEVEL_BITS-1:0] LEVEL_MAX     = {LEVEL_BITS{1'b1}};

    ///// pwm_counter rules /////
    // pwm_counter increments by 1 every clock.
    check_pwm_counter_step: assert property (
        @(posedge clk) $past(1'b1) |-> (pwm_counter == $past(pwm_counter) + 1)
    );

    // pwm_counter wraps to 0 after reaching max.
    check_pwm_counter_wrap: assert property (
        @(posedge clk) $past(1'b1) && ($past(pwm_counter) == LEVEL_MAX) |-> (pwm_counter == '0)
    );

    ///// fade_counter rules /////
    // When trigger is HIGH, fade_counter loads all 1s.
    check_fade_load_on_trigger_now: assert property (
        @(posedge clk) trigger |-> (fade_counter == FADE_ALL_ONES)
    );

    // When trigger is LOW and fade_counter was nonzero, it decrements by 1.
    check_fade_dec_when_nonzero: assert property (
        @(posedge clk) $past(1'b1) && !$past(trigger) && ($past(fade_counter) != '0) |-> (fade_counter == ($past(fade_counter) - 1))
    );

    // When trigger is LOW and fade_counter was zero, it stays zero.
    check_fade_hold_when_zero: assert property (
        @(posedge clk) $past(1'b1) && !$past(trigger) && ($past(fade_counter) == '0) |-> (fade_counter == '0)
    );

    // With trigger LOW in consecutive cycles, fade_counter is nonincreasing.
    check_fade_monotonic_no_trigger: assert property (
        @(posedge clk) $past(1'b1) && !$past(trigger) && !trigger |-> (fade_counter <= $past(fade_counter))
    );

    ///// level rules /////
    // level equals the top LEVEL_BITS of fade_counter.
    check_level_is_slice: assert property (
        @(posedge clk) level == fade_counter[FADE_BITS-1 -: LEVEL_BITS]
    );

    // With trigger LOW in consecutive cycles, level is nonincreasing.
    check_level_monotonic_no_trigger: assert property (
        @(posedge clk) $past(1'b1) && !$past(trigger) && !trigger |-> (level <= $past(level))
    );

    ///// drive rules /////
    // drive equals (pwm_counter < level).
    check_drive_is_compare: assert property (
        @(posedge clk) drive == (pwm_counter < level)
    );

    // When level is 0, drive must be 0.
    check_drive_zero_when_level_zero: assert property (
        @(posedge clk) (level == '0) |-> (drive == 1'b0)
    );

    // When level is max and pwm_counter != max, drive is 1.
    check_drive_one_when_level_max_and_pwm_not_max: assert property (
        @(posedge clk) (level == LEVEL_MAX) && (pwm_counter != LEVEL_MAX) |-> (drive == 1'b1)
    );

    // When level is max and pwm_counter is max, drive is 0.
    check_drive_zero_when_level_max_and_pwm_max: assert property (
        @(posedge clk) (level == LEVEL_MAX) && (pwm_counter == LEVEL_MAX) |-> (drive == 1'b0)
    );

    // While trigger is HIGH for 2 cycles, drive cannot be 0 in both cycles.
    check_no_two_consecutive_drive_zero_while_trigger_high: assert property (
        @(posedge clk) $past(1'b1) && trigger && $past(trigger) |-> !($past(drive) == 1'b0 && drive == 1'b0)
    );

endmodule