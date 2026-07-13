module calculator_sva (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [1:0] opcode,
    input logic [7:0] result
);

    localparam logic [1:0] OP_ADD = 2'b00;
    localparam logic [1:0] OP_SUB = 2'b01;
    localparam logic [1:0] OP_MUL = 2'b10;
    localparam logic [1:0] OP_DIV = 2'b11;

    // Addition opcode drives result to the 8-bit sum.
    check_addition_result: assert property (
        @($global_clock) (opcode == OP_ADD) |-> (result == 8'(a + b))
    );

    // Subtraction opcode drives result to the 8-bit difference.
    check_subtraction_result: assert property (
        @($global_clock) (opcode == OP_SUB) |-> (result == 8'(a - b))
    );

    // Multiplication opcode drives result to the low 8 bits of the product.
    check_multiplication_result: assert property (
        @($global_clock) (opcode == OP_MUL) |-> (result == 8'(a * b))
    );

    // Division opcode drives result to the quotient when the divisor is nonzero.
    check_division_result: assert property (
        @($global_clock) ((opcode == OP_DIV) && (b != 8'h00)) |-> (result == 8'(a / b))
    );

    // With defined inputs held constant, result remains constant.
    check_result_stable_when_inputs_stable: assert property (
        @($global_clock)
        ($stable(a) && $stable(b) && $stable(opcode) && !((opcode == OP_DIV) && (b == 8'h00)))
        |-> $stable(result)
    );

endmodule