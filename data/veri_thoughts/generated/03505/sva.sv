module calculator_sva (
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [1:0] op,
    input logic [7:0] result
);

    // Opcode 00 produces the 8-bit sum.
    check_addition_result: assert property (
        @($global_clock) (op == 2'b00) |-> (result == ((A + B) & 8'hFF))
    );

    // Opcode 01 produces the 8-bit difference.
    check_subtraction_result: assert property (
        @($global_clock) (op == 2'b01) |-> (result == ((A - B) & 8'hFF))
    );

    // Opcode 10 produces the low 8 bits of the product.
    check_multiplication_result: assert property (
        @($global_clock) (op == 2'b10) |-> (result == ((A * B) & 8'hFF))
    );

    // Opcode 11 with a nonzero divisor produces the quotient.
    check_division_result: assert property (
        @($global_clock) ((op == 2'b11) && (B != 8'h00)) |-> (result == (A / B))
    );

endmodule