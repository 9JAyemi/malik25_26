module motor_control_sva (
    input logic        clk,
    input logic        reset,
    input logic [15:0] input_signal,
    input logic [7:0]  motor_speed
);

    // A sampled reset must leave the output cleared by the next clock.
    check_reset_clears_motor_speed: assert property (
        @(posedge clk) reset |=> (motor_speed == 8'd0)
    );

    // Low-range inputs are scaled by 7 bits on the following cycle.
    check_low_range_scaling: assert property (
        @(posedge clk) disable iff (reset)
        (input_signal <= 16'd32767) |=> (motor_speed == $past(input_signal[14:7]))
    );

    // High-range inputs are scaled by 8 bits on the following cycle.
    check_high_range_scaling: assert property (
        @(posedge clk) disable iff (reset)
        (input_signal > 16'd32767) |=> (motor_speed == $past(input_signal[15:8]))
    );

    // The low-range threshold value maps to full-scale output.
    check_low_range_boundary: assert property (
        @(posedge clk) disable iff (reset)
        (input_signal == 16'h7FFF) |=> (motor_speed == 8'hFF)
    );

    // The first high-range value maps to 0x80.
    check_high_range_boundary: assert property (
        @(posedge clk) disable iff (reset)
        (input_signal == 16'h8000) |=> (motor_speed == 8'h80)
    );

endmodule