module PWM_sva (
    input logic clk,
    input logic [7:0] duty_cycle,
    input logic pwm_out,
    // Internal RTL signals (to be connected via bind)
    input logic [7:0] duty_count,
    input logic pwm_out_reg,
    input logic [7:0] period_count
);
    // Clock: clk (posedge). No reset in RTL (disable iff(1'b0) used).
    // Sequential logic with nonblocking updates; pwm_out is comb assign from pwm_out_reg.

    // pwm_out must mirror pwm_out_reg continuously.
    check_pwm_out_mirrors_reg: assert property (
        @(posedge clk) disable iff (1'b0) (pwm_out == pwm_out_reg)
    );

    // Next pwm_out_reg reflects prior (duty_count < duty_cycle).
    check_pwm_next_reflects_compare: assert property (
        @(posedge clk) disable iff (1'b0) 1'b1 |=> (pwm_out_reg == $past(duty_count < duty_cycle))
    );

    // When duty_count < duty_cycle, next pwm_out_reg is 1.
    check_pwm_high_on_lt: assert property (
        @(posedge clk) disable iff (1'b0) (duty_count < duty_cycle) |=> (pwm_out_reg == 1'b1)
    );

    // When duty_count >= duty_cycle, next pwm_out_reg is 0.
    check_pwm_low_on_ge: assert property (
        @(posedge clk) disable iff (1'b0) !(duty_count < duty_cycle) |=> (pwm_out_reg == 1'b0)
    );

    // Next duty_count equals (duty_count == period_count) ? 0 : duty_count + 1.
    check_duty_next_function: assert property (
        @(posedge clk) disable iff (1'b0)
            1'b1 |=> (duty_count == (($past(duty_count) == $past(period_count)) ? 8'd0 : ($past(duty_count) + 8'd1)))
    );

    // If duty_count equals period_count, next duty_count must be 0.
    check_duty_wrap_when_equal: assert property (
        @(posedge clk) disable iff (1'b0) (duty_count == period_count) |=> (duty_count == 8'd0)
    );

    // If duty_count does not equal period_count, next duty_count increments by 1 (mod 256).
    check_duty_inc_when_not_equal: assert property (
        @(posedge clk) disable iff (1'b0) (duty_count != period_count) |=> (duty_count == ($past(duty_count) + 8'd1))
    );

    // If duty_cycle is zero, next pwm_out_reg must be 0.
    check_zero_duty_forces_low: assert property (
        @(posedge clk) disable iff (1'b0) (duty_cycle == 8'd0) |=> (pwm_out_reg == 1'b0)
    );

    // pwm_out and pwm_out_reg have matching change activity across cycles.
    check_pwm_change_matches_reg: assert property (
        @(posedge clk) disable iff (1'b0) 1'b1 |=> ($changed(pwm_out) == $changed(pwm_out_reg))
    );

    // On wrap condition, next duty_count is 0 and pwm_out_reg reflects (period_count < duty_cycle) from prior cycle.
    check_wrap_coupled_outputs: assert property (
        @(posedge clk) disable iff (1'b0)
            (duty_count == period_count) |=> ((duty_count == 8'd0) && (pwm_out_reg == $past(period_count < duty_cycle)))
    );

endmodule