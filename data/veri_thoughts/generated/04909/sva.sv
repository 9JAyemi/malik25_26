module division_sva (
    input logic       clk,
    input logic [3:0] dividend,
    input logic [3:0] divisor,
    input logic [3:0] quotient,
    input logic [3:0] remainder
);

    // Combinational divider sampled with external clk; RTL has no reset.

    // Divide-by-zero drives zero outputs.
    check_divide_by_zero_outputs_zero: assert property (
        @(posedge clk) (divisor == 4'b0000) |-> ((quotient == 4'b0000) && (remainder == 4'b0000))
    );

    // Nonzero divisor produces the integer quotient.
    check_nonzero_divisor_quotient: assert property (
        @(posedge clk) (divisor != 4'b0000) |-> (quotient == (dividend / divisor))
    );

    // Nonzero divisor produces the integer remainder.
    check_nonzero_divisor_remainder: assert property (
        @(posedge clk) (divisor != 4'b0000) |-> (remainder == (dividend % divisor))
    );

    // Remainder stays below the divisor.
    check_remainder_less_than_divisor: assert property (
        @(posedge clk) (divisor != 4'b0000) |-> (remainder < divisor)
    );

    // Quotient and remainder reconstruct the dividend.
    check_division_identity: assert property (
        @(posedge clk) (divisor != 4'b0000) |-> (((quotient * divisor) + remainder) == dividend)
    );

    // Smaller dividend gives zero quotient and pass-through remainder.
    check_smaller_dividend_behavior: assert property (
        @(posedge clk) ((divisor != 4'b0000) && (dividend < divisor)) |-> ((quotient == 4'b0000) && (remainder == dividend))
    );

    // Dividing by one passes dividend to quotient with zero remainder.
    check_divisor_one_behavior: assert property (
        @(posedge clk) (divisor == 4'b0001) |-> ((quotient == dividend) && (remainder == 4'b0000))
    );

    // Zero dividend produces zero outputs.
    check_zero_dividend_behavior: assert property (
        @(posedge clk) (dividend == 4'b0000) |-> ((quotient == 4'b0000) && (remainder == 4'b0000))
    );

endmodule