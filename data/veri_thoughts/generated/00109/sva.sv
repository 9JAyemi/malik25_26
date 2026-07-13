module absolute_value_sva (
    input logic clk,
    input logic signed [31:0] in,
    input logic signed [31:0] out
);

    // Output matches the implemented conditional expression.
    check_absolute_value_function: assert property (
        @(posedge clk) out == ((in < 32'sd0) ? -in : in)
    );

    // Non-negative inputs pass through unchanged.
    check_nonnegative_passthrough: assert property (
        @(posedge clk) (in >= 32'sd0) |-> (out == in)
    );

    // Negative inputs produce the two's-complement negation.
    check_negative_negation: assert property (
        @(posedge clk) (in < 32'sd0) |-> (out == -in)
    );

    // Zero maps to zero.
    check_zero_maps_to_zero: assert property (
        @(posedge clk) (in == 32'sd0) |-> (out == 32'sd0)
    );

    // The most-negative input remains unchanged after negation overflow.
    check_min_negative_corner_case: assert property (
        @(posedge clk) (in == 32'sh80000000) |-> (out == 32'sh80000000)
    );

    // Negative inputs other than the minimum value yield non-negative outputs.
    check_negative_nonmin_yields_nonnegative: assert property (
        @(posedge clk) ((in < 32'sd0) && (in != 32'sh80000000)) |-> (out >= 32'sd0)
    );

endmodule