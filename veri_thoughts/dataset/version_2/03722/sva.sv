module PWM_sva (
    input logic clk,
    input logic \ref ,
    input logic [7:0] duty,
    input logic pwm,
    input logic [7:0] count,
    input logic [7:0] threshold
);

    // Threshold follows the RTL duty scaling with period fixed at 256.
    check_threshold_matches_duty: assert property (
        @(posedge clk) disable iff ($initstate)
        threshold == duty
    );

    // Count increments every clock and wraps from 255 to 0.
    check_count_increments_and_wraps: assert property (
        @(posedge clk) disable iff ($initstate)
        count == (($past(count) == 8'hFF) ? 8'h00 : ($past(count) + 8'h01))
    );

    // PWM goes high when the previous count was below threshold.
    check_pwm_high_below_threshold: assert property (
        @(posedge clk) disable iff ($initstate)
        ($past(count) < $past(threshold)) |-> (pwm == 1'b1)
    );

    // PWM goes low when the previous count was at or above threshold.
    check_pwm_low_at_or_above_threshold: assert property (
        @(posedge clk) disable iff ($initstate)
        ($past(count) >= $past(threshold)) |-> (pwm == 1'b0)
    );

    // Zero duty forces PWM low on the following cycle.
    check_zero_duty_forces_low: assert property (
        @(posedge clk) disable iff ($initstate)
        (duty == 8'h00) |=> (pwm == 1'b0)
    );

    // At full duty, a low PWM cycle is followed by a high cycle.
    check_full_duty_low_cycle_is_single: assert property (
        @(posedge clk) disable iff ($initstate)
        (duty == 8'hFF && $past(duty) == 8'hFF && pwm == 1'b0) |=> (pwm == 1'b1)
    );

    // At duty 1, a high PWM cycle is followed by a low cycle.
    check_duty_one_high_cycle_is_single: assert property (
        @(posedge clk) disable iff ($initstate)
        (duty == 8'h01 && $past(duty) == 8'h01 && pwm == 1'b1) |=> (pwm == 1'b0)
    );

endmodule