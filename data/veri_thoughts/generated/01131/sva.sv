module abs_value_sva (
    input logic CLK,
    input logic signed [31:0] in,
    input logic [31:0] out
);
    // For negative input, output equals two's complement of input.
    check_neg_twos_complement: assert property (
        @(posedge CLK) (in < 0) |-> (out == ((~in) + 32'sd1))
    );

    // For non-negative input, output equals input.
    check_nonneg_passthrough: assert property (
        @(posedge CLK) (in >= 0) |-> (out == in)
    );

    // Functional equivalence to the conditional expression in RTL.
    check_function_equivalence: assert property (
        @(posedge CLK) out == ((in < 0) ? ((~in) + 32'sd1) : in)
    );

    // For negative input, output plus input sums to zero (mod 32 bits).
    check_neg_sum_zero: assert property (
        @(posedge CLK) (in < 0) |-> ((out + in) == 32'h0000_0000)
    );

    // Zero input maps to zero output.
    check_zero_maps_to_zero: assert property (
        @(posedge CLK) (in == 32'sh0000_0000) |-> (out == 32'h0000_0000)
    );

    // Minimum negative value maps to itself after two's complement.
    check_minint_maps_to_self: assert property (
        @(posedge CLK) (in == 32'sh8000_0000) |-> (out == 32'h8000_0000)
    );

    // For non-negative input, output MSB is zero.
    check_nonneg_out_msb_zero: assert property (
        @(posedge CLK) (in >= 0) |-> (out[31] == 1'b0)
    );

    // For negative non-minint input, output MSB is zero (positive magnitude).
    check_neg_nonmin_out_msb_zero: assert property (
        @(posedge CLK) ((in < 0) && (in != 32'sh8000_0000)) |-> (out[31] == 1'b0)
    );
endmodule