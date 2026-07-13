module calculator_assertions (
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [1:0] op,
    input logic [7:0] result
);

    // Addition mode returns the truncated sum of A and B.
    check_addition_result: assert property (
        @($global_clock) (op == 2'b00) |-> (result == ((A + B) & 8'hFF))
    );

    // Subtraction mode returns the truncated difference of A and B.
    check_subtraction_result: assert property (
        @($global_clock) (op == 2'b01) |-> (result == ((A - B) & 8'hFF))
    );

    // Multiplication mode returns the low 8 bits of the product.
    check_multiplication_result: assert property (
        @($global_clock) (op == 2'b10) |-> (result == ((A * B) & 8'hFF))
    );

    // Division by zero returns zero.
    check_divide_by_zero_result: assert property (
        @($global_clock) ((op == 2'b11) && (B == 8'h00)) |-> (result == 8'h00)
    );

    // Division mode returns the quotient when the divisor is nonzero.
    check_division_result: assert property (
        @($global_clock) ((op == 2'b11) && (B != 8'h00)) |-> (result == ((A / B) & 8'hFF))
    );

    // Stable inputs keep the combinational result stable.
    check_stable_inputs_stable_result: assert property (
        @($global_clock) $stable({A, B, op}) |-> $stable(result)
    );

endmodule