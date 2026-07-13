module calculator_sva (
    input logic [7:0] num1,
    input logic [7:0] num2,
    input logic [1:0] op,
    input logic [7:0] result
);

    // Addition mode returns the low 8 bits of num1 + num2.
    check_add_result: assert property (
        @($global_clock) (op == 2'b00) |-> (result == ((num1 + num2) & 8'hFF))
    );

    // Subtraction mode returns the low 8 bits of num1 - num2.
    check_sub_result: assert property (
        @($global_clock) (op == 2'b01) |-> (result == ((num1 - num2) & 8'hFF))
    );

    // Multiplication mode returns the low 8 bits of num1 * num2.
    check_mul_result: assert property (
        @($global_clock) (op == 2'b10) |-> (result == ((num1 * num2) & 8'hFF))
    );

    // Division by zero forces the result to zero.
    check_div_zero_result: assert property (
        @($global_clock) ((op == 2'b11) && (num2 == 8'h00)) |-> (result == 8'h00)
    );

    // Division mode returns the low 8 bits of num1 / num2 when num2 is nonzero.
    check_div_nonzero_result: assert property (
        @($global_clock) ((op == 2'b11) && (num2 != 8'h00)) |-> (result == ((num1 / num2) & 8'hFF))
    );

endmodule