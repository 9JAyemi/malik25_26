module calculator_sva (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [1:0] op,
    input logic [7:0] result
);

    // Addition mode drives result to the 8-bit sum of a and b.
    check_addition_mode: assert property (
        @($global_clock)
        (op == 2'b00) |-> (result == ((a + b) & 8'hFF))
    );

    // Subtraction mode drives result to the 8-bit difference of a and b.
    check_subtraction_mode: assert property (
        @($global_clock)
        (op == 2'b01) |-> (result == ((a - b) & 8'hFF))
    );

    // Multiplication mode drives result to the low 8 bits of a*b when the product is 8 bits or less.
    check_multiplication_mode_low: assert property (
        @($global_clock)
        ((op == 2'b10) && (((a * b) & 16'hFF00) == 16'h0000)) |-> (result == ((a * b) & 8'hFF))
    );

    // Multiplication mode drives 8'hFF when the product exceeds 8 bits.
    check_multiplication_mode_overflow: assert property (
        @($global_clock)
        ((op == 2'b10) && (((a * b) & 16'hFF00) != 16'h0000)) |-> (result == 8'hFF)
    );

    // Division mode drives 8'hFF when the divisor is zero.
    check_division_mode_divide_by_zero: assert property (
        @($global_clock)
        ((op == 2'b11) && (b == 8'h00)) |-> (result == 8'hFF)
    );

    // Division mode drives result to the low 8 bits of a divided by b when the quotient is 8 bits or less.
    check_division_mode_low: assert property (
        @($global_clock)
        ((op == 2'b11) && (b != 8'h00) && (((a / b) & 8'hFF) == (a / b))) |-> (result == ((a / b) & 8'hFF))
    );

    // Division mode drives 8'hFF when the quotient exceeds 8 bits.
    check_division_mode_overflow: assert property (
        @($global_clock)
        ((op == 2'b11) && (b != 8'h00) && (((a / b) & 8'hFF) != (a / b))) |-> (result == 8'hFF)
    );

endmodule