module motor_controller_sva (
    input logic clk,
    input logic rst,
    input logic [7:0] speed,
    input logic [7:0] motor_speed
);
    ///// Reset behavior /////
    // During reset, motor_speed is forced to zero.
    check_reset_forces_zero: assert property (
        @(posedge clk) rst |-> (motor_speed == 8'd0)
    );

    // While reset stays asserted across cycles, motor_speed remains zero.
    check_zero_while_reset_held: assert property (
        @(posedge clk) (rst && $past(rst)) |-> (motor_speed == 8'd0)
    );

    // On a falling edge of reset, output at this sample is zero (held from prior reset cycle).
    check_output_zero_on_reset_fall_sample: assert property (
        @(posedge clk) $fell(rst) |-> (motor_speed == 8'd0)
    );

    // On a rising edge of reset, async reset clears output to zero by this sample.
    check_output_zero_on_reset_rise_sample: assert property (
        @(posedge clk) $rose(rst) |-> (motor_speed == 8'd0)
    );

    ///// Functional behavior /////
    // When not in/reset for prior cycle, motor_speed equals previous cycle's speed.
    check_capture_prev_speed: assert property (
        @(posedge clk) disable iff (rst) (!$past(rst)) |-> (motor_speed == $past(speed))
    );

    // If out of reset for two cycles and input unchanged between them, output is stable.
    check_output_stable_when_input_stable: assert property (
        @(posedge clk) disable iff (rst) (!$past(rst) && !$past(rst,2) && ($past(speed) == $past(speed,2))) |-> (motor_speed == $past(motor_speed))
    );

    // If out of reset for two cycles and output changed, input must have changed in the prior cycle.
    check_output_change_requires_input_change: assert property (
        @(posedge clk) disable iff (rst) (!$past(rst) && !$past(rst,2) && (motor_speed != $past(motor_speed))) |-> ($past(speed) != $past(speed,2))
    );

    // If out of reset and motor_speed is zero, prior cycle's speed must have been zero.
    check_output_zero_means_prior_input_zero: assert property (
        @(posedge clk) disable iff (rst) (!$past(rst) && (motor_speed == 8'd0)) |-> ($past(speed) == 8'd0)
    );
endmodule