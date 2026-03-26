module LCB_sva #(
    parameter integer pwm_width = 8,
    parameter integer pwm_frequency = 100
) (
    input logic clk,
    input logic [1:0] analog_signal,
    input logic enable,
    input logic reset,
    input logic pwm_out,
    input logic [pwm_width-1:0] pwm_counter,
    input logic [pwm_width-1:0] pwm_threshold
);

    localparam logic [pwm_width-1:0] PWM_ZERO  = {pwm_width{1'b0}};
    localparam logic [pwm_width-1:0] PWM_ONE   = {{(pwm_width-1){1'b0}}, 1'b1};
    localparam logic [pwm_width-1:0] PWM_MAX   = {pwm_width{1'b1}};
    localparam logic [pwm_width-1:0] THRESH_00 = pwm_width / 8;
    localparam logic [pwm_width-1:0] THRESH_01 = pwm_width / 4;
    localparam logic [pwm_width-1:0] THRESH_10 = pwm_width / 2;
    localparam logic [pwm_width-1:0] THRESH_11 = pwm_width - 1;

    // Reset drives the counter to zero.
    check_reset_clears_counter: assert property (
        @(posedge clk) reset |-> (pwm_counter == PWM_ZERO)
    );

    // Reset drives the threshold to zero.
    check_reset_clears_threshold: assert property (
        @(posedge clk) reset |-> (pwm_threshold == PWM_ZERO)
    );

    // Reset drives the PWM output low.
    check_reset_clears_pwm_out: assert property (
        @(posedge clk) reset |-> (pwm_out == 1'b0)
    );

    // The counter holds when enable is low.
    check_counter_holds_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        !enable |=> (pwm_counter == $past(pwm_counter))
    );

    // The counter increments by one when enabled below max.
    check_counter_increments_when_enabled: assert property (
        @(posedge clk) disable iff (reset)
        enable && (pwm_counter != PWM_MAX) |=> (pwm_counter == ($past(pwm_counter) + PWM_ONE))
    );

    // The counter wraps to zero when enabled at max.
    check_counter_wraps_at_max: assert property (
        @(posedge clk) disable iff (reset)
        enable && (pwm_counter == PWM_MAX) |=> (pwm_counter == PWM_ZERO)
    );

    // analog_signal 00 selects pwm_width/8 as the threshold.
    check_threshold_for_analog_00: assert property (
        @(posedge clk) disable iff (reset)
        (analog_signal == 2'b00) |=> (pwm_threshold == THRESH_00)
    );

    // analog_signal 01 selects pwm_width/4 as the threshold.
    check_threshold_for_analog_01: assert property (
        @(posedge clk) disable iff (reset)
        (analog_signal == 2'b01) |=> (pwm_threshold == THRESH_01)
    );

    // analog_signal 10 selects pwm_width/2 as the threshold.
    check_threshold_for_analog_10: assert property (
        @(posedge clk) disable iff (reset)
        (analog_signal == 2'b10) |=> (pwm_threshold == THRESH_10)
    );

    // analog_signal 11 selects pwm_width-1 as the threshold.
    check_threshold_for_analog_11: assert property (
        @(posedge clk) disable iff (reset)
        (analog_signal == 2'b11) |=> (pwm_threshold == THRESH_11)
    );

    // The PWM output holds when enable is low.
    check_pwm_out_holds_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        !enable |=> (pwm_out == $past(pwm_out))
    );

    // The PWM output goes high when enabled and counter meets the threshold.
    check_pwm_out_high_when_counter_ge_threshold: assert property (
        @(posedge clk) disable iff (reset)
        enable && (pwm_counter >= pwm_threshold) |=> (pwm_out == 1'b1)
    );

    // The PWM output goes low when enabled and counter is below the threshold.
    check_pwm_out_low_when_counter_lt_threshold: assert property (
        @(posedge clk) disable iff (reset)
        enable && (pwm_counter < pwm_threshold) |=> (pwm_out == 1'b0)
    );

endmodule