module pwm_generator_sva (
    input logic clk,
    input logic [3:0] duty_cycle,
    input logic pwm_out,
    input logic [3:0] counter
);

    // Counter increments by one on non-wrap cycles.
    check_counter_increments: assert property (
        @(posedge clk) (counter < 4'd15) |=> (counter == ($past(counter) + 4'd1))
    );

    // At the wrap point, counter returns to zero and pwm_out uses the sampled comparison.
    check_wrap_behavior: assert property (
        @(posedge clk) (counter == 4'd15) |=> ((counter == 4'd0) && (pwm_out == ($past(counter) < $past(duty_cycle))))
    );

    // pwm_out holds its value on cycles where the wrap condition is not met.
    check_pwm_holds_between_wraps: assert property (
        @(posedge clk) (counter < 4'd15) |=> (pwm_out == $past(pwm_out))
    );

    // The sampled wrap comparison always drives pwm_out low for a 4-bit duty_cycle.
    check_pwm_low_on_wrap: assert property (
        @(posedge clk) (counter == 4'd15) |=> (pwm_out == 1'b0)
    );

endmodule