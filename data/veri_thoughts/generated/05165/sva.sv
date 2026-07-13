module binary_counter_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] counter_out
);

    // Clock: clk
    // Reset: reset, active-high asynchronous
    // Logic: sequential

    // Reset drives the counter output to zero.
    reset_clears_counter_out: assert property (
        @(posedge clk) disable iff ($initstate)
        reset |-> (counter_out == 4'b0000)
    );

    // Any nonzero sampled count must be the prior sampled count plus one.
    nonzero_count_is_prior_plus_one: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        (counter_out != 4'b0000) |-> (counter_out == ($past(counter_out) + 4'd1))
    );

    // A sampled decrease can only occur when the count lands at zero.
    sampled_decrease_only_to_zero: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        (counter_out < $past(counter_out)) |-> (counter_out == 4'b0000)
    );

endmodule

module pwm_generator_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] counter_out,
    input logic [3:0] adc_in,
    input logic select,
    input logic pwm_out,
    input logic [3:0] mux_out,
    input logic comparator_out
);

    // Clock: clk
    // Reset: reset, active-high asynchronous
    // Logic: mixed; mux/comparator are combinational, pwm_out is sequential

    // Reset drives the PWM output low.
    reset_clears_pwm_out: assert property (
        @(posedge clk) disable iff ($initstate)
        reset |-> (pwm_out == 1'b0)
    );

    // Comparator output matches the greater-or-equal comparison.
    comparator_matches_ge_compare: assert property (
        @(posedge clk) disable iff (reset)
        comparator_out == (mux_out >= adc_in)
    );

    // A high PWM output turns off on the next cycle when comparator_out is low.
    turn_off_when_comparator_low: assert property (
        @(posedge clk) disable iff (reset)
        (pwm_out == 1'b1 && comparator_out == 1'b0) |=> (pwm_out == 1'b0)
    );

    // A low PWM output stays low on the next cycle when comparator_out is low.
    stay_low_when_comparator_low: assert property (
        @(posedge clk) disable iff (reset)
        (pwm_out == 1'b0 && comparator_out == 1'b0) |=> (pwm_out == 1'b0)
    );

    // A sampled high PWM state requires comparator_out to have been high previously.
    pwm_high_requires_prev_comparator_high: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        (pwm_out == 1'b1) |-> ($past(comparator_out) == 1'b1)
    );

    // PWM can only rise when comparator_out was high in the prior cycle.
    pwm_rise_requires_prev_comparator_high: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        $rose(pwm_out) |-> ($past(comparator_out) == 1'b1)
    );

endmodule