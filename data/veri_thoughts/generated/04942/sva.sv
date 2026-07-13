module absolute_value_calculator_sva #(
    parameter n = 8
) (
    input logic clk,
    input logic signed [n-1:0] input_signal,
    input logic [n-1:0] output_signal
);

    localparam logic [n-1:0] MIN_NEG = {1'b1, {n-1{1'b0}}};

    // Output always matches the implemented absolute-value expression.
    check_absolute_value_function: assert property (
        @(posedge clk)
        output_signal == (input_signal[n-1] ? (~input_signal + 1'b1) : input_signal)
    );

    // Non-negative inputs pass through unchanged.
    check_non_negative_passthrough: assert property (
        @(posedge clk)
        !input_signal[n-1] |-> (output_signal == input_signal)
    );

    // Negative inputs are converted with two's-complement negation.
    check_negative_twos_complement: assert property (
        @(posedge clk)
        input_signal[n-1] |-> (output_signal == (~input_signal + 1'b1))
    );

    // Zero maps to zero.
    check_zero_maps_to_zero: assert property (
        @(posedge clk)
        (input_signal == '0) |-> (output_signal == '0)
    );

    // The most-negative input remains unchanged by two's-complement negation.
    check_min_negative_corner: assert property (
        @(posedge clk)
        (input_signal == MIN_NEG) |-> (output_signal == MIN_NEG)
    );

    // Negative inputs other than the minimum value produce a non-negative result.
    check_negative_non_min_sign_clear: assert property (
        @(posedge clk)
        (input_signal[n-1] && (input_signal != MIN_NEG)) |-> (output_signal[n-1] == 1'b0)
    );

    // Non-negative inputs produce a non-negative result.
    check_non_negative_sign_clear: assert property (
        @(posedge clk)
        !input_signal[n-1] |-> (output_signal[n-1] == 1'b0)
    );

endmodule