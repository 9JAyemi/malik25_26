module binary_divider_sva (
    input logic [15:0] dividend,
    input logic [15:0] divisor,
    input logic [15:0] quotient,
    input logic [15:0] remainder
);

    // Division by zero drives both outputs to the maximum 16-bit value.
    check_divide_by_zero_outputs_max: assert property (
        @($global_clock)
        (divisor == 16'd0) |-> ((quotient == 16'hFFFF) && (remainder == 16'hFFFF))
    );

    // For a nonzero divisor, quotient and remainder match the arithmetic operators.
    check_nonzero_divisor_exact_results: assert property (
        @($global_clock)
        (divisor != 16'd0) |-> ((quotient == (dividend / divisor)) && (remainder == (dividend % divisor)))
    );

    // For a nonzero divisor, remainder is always less than the divisor.
    check_nonzero_divisor_remainder_range: assert property (
        @($global_clock)
        (divisor != 16'd0) |-> (remainder < divisor)
    );

    // For a nonzero divisor, quotient*divisor plus remainder reconstructs dividend.
    check_nonzero_divisor_reconstructs_dividend: assert property (
        @($global_clock)
        (divisor != 16'd0) |-> ({16'd0, dividend} == (({16'd0, quotient} * {16'd0, divisor}) + {16'd0, remainder}))
    );

    // If the divisor is larger than the dividend, quotient is zero and remainder is the dividend.
    check_divisor_larger_than_dividend: assert property (
        @($global_clock)
        ((divisor != 16'd0) && (divisor > dividend)) |-> ((quotient == 16'd0) && (remainder == dividend))
    );

    // Dividing by one returns the dividend with zero remainder.
    check_divisor_one_identity: assert property (
        @($global_clock)
        (divisor == 16'd1) |-> ((quotient == dividend) && (remainder == 16'd0))
    );

endmodule