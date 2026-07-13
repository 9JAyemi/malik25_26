module servo_control_block_sva #(
    parameter integer freq     = 50,
    parameter integer duty_min = 5,
    parameter integer duty_max = 10,
    parameter integer pos_min  = 0,
    parameter integer pos_max  = 1023
) (
    input logic [9:0]  pos_desired,
    input logic [9:0]  pos_current,
    input logic        clk,
    input logic        pwm_out,
    input logic [9:0]  pos_diff,
    input logic [31:0] pwm_period,
    input logic [31:0] pwm_counter,
    input logic [9:0]  duty_cycle
);

    // pos_diff matches the 10-bit position subtraction.
    check_pos_diff_calculation: assert property (
        @(posedge clk) pos_diff == (pos_desired - pos_current)
    );

    // pwm_period is the constant period derived from freq.
    check_pwm_period_calculation: assert property (
        @(posedge clk) pwm_period == (200000000 / freq)
    );

    // duty_cycle follows the RTL arithmetic based on pos_diff.
    check_duty_cycle_calculation: assert property (
        @(posedge clk) duty_cycle == ((((duty_max - duty_min) * (pos_max - pos_diff)) / (pos_max - pos_min)) + duty_min)
    );

    // duty_cycle stays within the configured min and max.
    check_duty_cycle_range: assert property (
        @(posedge clk) (duty_cycle >= duty_min) && (duty_cycle <= duty_max)
    );

    // Matching positions produce the maximum duty cycle.
    check_max_duty_when_positions_match: assert property (
        @(posedge clk) (pos_desired == pos_current) |-> (duty_cycle == duty_max)
    );

    // Full-scale pos_diff produces the minimum duty cycle.
    check_min_duty_at_full_scale_diff: assert property (
        @(posedge clk) (pos_diff == pos_max) |-> (duty_cycle == duty_min)
    );

    // Below pwm_period, the counter increments by one on the next clock.
    check_counter_increments_below_period: assert property (
        @(posedge clk) (pwm_counter < pwm_period) |=> (pwm_counter == ($past(pwm_counter) + 32'd1))
    );

    // At or above pwm_period, the counter resets to zero on the next clock.
    check_counter_wraps_at_period: assert property (
        @(posedge clk) (pwm_counter >= pwm_period) |=> (pwm_counter == 32'd0)
    );

    // After one update, the counter is always driven into the valid range.
    check_counter_bounded_after_update: assert property (
        @(posedge clk) 1'b1 |=> (pwm_counter <= pwm_period)
    );

    // A counter value below the compare threshold drives pwm_out high next cycle.
    check_pwm_high_below_threshold: assert property (
        @(posedge clk) (pwm_counter < (pwm_period * duty_cycle)) |=> (pwm_out == 1'b1)
    );

    // A counter value at or above the compare threshold drives pwm_out low next cycle.
    check_pwm_low_at_or_above_threshold: assert property (
        @(posedge clk) (pwm_counter >= (pwm_period * duty_cycle)) |=> (pwm_out == 1'b0)
    );

endmodule