module calculator_sva (
    input logic clk,
    input logic [7:0] num1,
    input logic [7:0] num2,
    input logic [1:0] op,
    input logic [7:0] result
);

    // Combinational RTL with no reset; clk is a sampling clock.

    // Addition mode returns the 8-bit sum.
    check_addition_result: assert property (
        @(posedge clk) (op == 2'b00) |-> (result == ((num1 + num2) & 8'hFF))
    );

    // Subtraction mode returns the 8-bit difference.
    check_subtraction_result: assert property (
        @(posedge clk) (op == 2'b01) |-> (result == ((num1 - num2) & 8'hFF))
    );

    // Multiplication mode returns the low 8 bits of the product.
    check_multiplication_result: assert property (
        @(posedge clk) (op == 2'b10) |-> (result == ((num1 * num2) & 8'hFF))
    );

    // Division by zero forces the result to zero.
    check_division_by_zero_result: assert property (
        @(posedge clk) (op == 2'b11 && num2 == 8'h00) |-> (result == 8'h00)
    );

    // Division mode returns the integer quotient for a nonzero divisor.
    check_division_result: assert property (
        @(posedge clk) (op == 2'b11 && num2 != 8'h00) |-> (result == (num1 / num2))
    );

endmodule