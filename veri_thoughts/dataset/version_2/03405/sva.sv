module temp_sensor_sva (
    input logic signed [9:0]  temp_C,
    input logic               reset,
    input logic signed [15:0] temp_F
);

    // During reset, the output is cleared to zero.
    check_reset_forces_zero: assert property (
        @($global_clock) disable iff (!reset)
        temp_F == 16'sd0
    );

    // Outside reset, the output matches the RTL conversion expression.
    check_conversion_formula: assert property (
        @($global_clock) disable iff (reset)
        temp_F == ((temp_C * 2) + 32)
    );

    // Zero Celsius produces an output of 32.
    check_zero_celsius_offset: assert property (
        @($global_clock) disable iff (reset)
        (temp_C == 10'sd0) |-> (temp_F == 16'sd32)
    );

    // Negative sixteen Celsius produces an output of zero.
    check_minus16_celsius_zero_point: assert property (
        @($global_clock) disable iff (reset)
        (temp_C == -10'sd16) |-> (temp_F == 16'sd0)
    );

    // The implemented expression always yields an even output.
    check_output_is_even: assert property (
        @($global_clock) disable iff (reset)
        temp_F[0] == 1'b0
    );

    // Outside reset, the output stays within the range implied by the 10-bit input.
    check_output_range: assert property (
        @($global_clock) disable iff (reset)
        (temp_F >= -16'sd992) && (temp_F <= 16'sd1054)
    );

endmodule