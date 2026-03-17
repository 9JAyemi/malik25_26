module calculator_sva (
    input logic       clk,
    input logic [7:0] num1,
    input logic [7:0] num2,
    input logic [1:0] op,
    input logic [7:0] result
);

    // Opcode 00 produces the low 8 bits of the sum.
    check_add_result: assert property (
        @(posedge clk)
        (op == 2'b00) |-> ({1'b0, result} == (({1'b0, num1} + {1'b0, num2}) & 9'h0ff))
    );

    // Opcode 01 produces the low 8 bits of the difference.
    check_subtract_result: assert property (
        @(posedge clk)
        (op == 2'b01) |-> ({1'b0, result} == (({1'b0, num1} - {1'b0, num2}) & 9'h0ff))
    );

    // Opcode 10 produces the low 8 bits of the product.
    check_multiply_result: assert property (
        @(posedge clk)
        (op == 2'b10) |-> ({8'b0, result} == (({8'b0, num1} * {8'b0, num2}) & 16'h00ff))
    );

    // Opcode 11 produces the quotient when the divisor is nonzero.
    check_divide_result: assert property (
        @(posedge clk)
        (op == 2'b11 && num2 != 8'h00) |-> ({8'b0, result} == ({8'b0, num1} / {8'b0, num2}))
    );

    // Repeating the same sampled inputs must reproduce the same result.
    check_same_inputs_same_result: assert property (
        @(posedge clk)
        $past(1'b1) && ({num1, num2, op} == $past({num1, num2, op})) |-> (result == $past(result))
    );

endmodule