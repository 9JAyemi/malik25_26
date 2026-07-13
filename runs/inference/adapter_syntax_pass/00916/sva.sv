module calculator_sva (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [1:0] op,
    input logic [7:0] result
);

    // Addition mode drives result to the 8-bit sum of a and b.
    check_addition_mode: assert property (
        @($global_clock) (op == 2'b00) |-> (result == ((a + b) & 8'hFF))
    );

    // Subtraction mode drives result to the 8-bit difference of a and b.
    check_subtraction_mode: assert property (
        @($global_clock) (op == 2'b01) |-> (result == ((a - b) & 8'hFF))
    );

    // Multiplication mode drives result to the low 8 bits of the product.
    check_multiplication_mode: assert property (
        @($global_clock) (op == 2'b10) |-> (result == ((a * b) & 8'hFF))
    );

    // Division mode drives result to the quotient when the divisor is nonzero.
    check_division_mode: assert property (
        @($global_clock) ((op == 2'b11) && (b != 8'h00)) |-> (result == ((a / b) & 8'hFF))
    );

endmodule