module calculator_sva (
    input logic [7:0] num1,
    input logic [7:0] num2,
    input logic [1:0] op,
    input logic [7:0] result
);

    // Addition mode drives result to num1 + num2.
    check_addition_mode: assert property (
        @($global_clock) (op == 2'b00) |-> (result == (num1 + num2))
    );

    // Subtraction mode drives result to num1 - num2.
    check_subtraction_mode: assert property (
        @($global_clock) (op == 2'b01) |-> (result == (num1 - num2))
    );

    // Multiplication mode drives result to num1 * num2.
    check_multiplication_mode: assert property (
        @($global_clock) (op == 2'b10) |-> (result == (num1 * num2))
    );

    // Division by zero forces result to zero.
    check_division_by_zero: assert property (
        @($global_clock) ((op == 2'b11) && (num2 == 8'h00)) |-> (result == 8'h00)
    );

    // Division mode drives result to num1 / num2 when num2 is nonzero.
    check_division_mode: assert property (
        @($global_clock) ((op == 2'b11) && (num2 != 8'h00)) |-> (result == (num1 / num2))
    );

endmodule