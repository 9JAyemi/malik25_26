module abs_calc_sva (
    input logic CLK,
    input logic signed [31:0] in,
    input logic [31:0] out
);
    // Output equals absolute value: out = in if in>=0 else (~in+1).
    check_abs_function: assert property (
        @(posedge CLK) out == ((in >= 32'sd0) ? $unsigned(in) : $unsigned(~in + 32'sd1))
    );

    // Non-negative input passes through unchanged.
    check_nonneg_passthrough: assert property (
        @(posedge CLK) (in >= 32'sd0) |-> (out == $unsigned(in))
    );

    // Negative input produces two's complement magnitude.
    check_neg_twos_complement: assert property (
        @(posedge CLK) (in < 32'sd0) |-> (out == $unsigned(~in + 32'sd1))
    );

    // Zero input yields zero output.
    check_zero_out_zero: assert property (
        @(posedge CLK) (in == 32'sd0) |-> (out == 32'd0)
    );

    // Most-negative value maps to itself (two's complement wrap).
    check_minint_edgecase: assert property (
        @(posedge CLK) (in == 32'sh80000000) |-> (out == 32'h80000000)
    );

    // For negative inputs except most-negative, MSB of output is 0.
    check_neg_not_min_msb0: assert property (
        @(posedge CLK) ((in < 32'sd0) && (in != 32'sh80000000)) |-> (out[31] == 1'b0)
    );

    // For non-negative inputs, MSB of output is 0.
    check_nonneg_msb0: assert property (
        @(posedge CLK) (in >= 32'sd0) |-> (out[31] == 1'b0)
    );

    // For negative inputs except most-negative, output differs from input.
    check_neg_not_min_out_neq_in: assert property (
        @(posedge CLK) ((in < 32'sd0) && (in != 32'sh80000000)) |-> (out != $unsigned(in))
    );

    // If output equals input, then input was non-negative or most-negative.
    check_out_eq_in_implies_sign_condition: assert property (
        @(posedge CLK) (out == $unsigned(in)) |-> ((in >= 32'sd0) || (in == 32'sh80000000))
    );

    // For negative inputs except most-negative, output is non-zero.
    check_neg_not_min_out_nonzero: assert property (
        @(posedge CLK) ((in < 32'sd0) && (in != 32'sh80000000)) |-> (out != 32'd0)
    );
endmodule