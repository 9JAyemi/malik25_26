module calculator_sva (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [1:0] op,
    input logic [7:0] result
);

    // Addition opcode drives the low 8 bits of a + b.
    check_add_result: assert property (
        @($global_clock) (op == 2'b00) |-> (result == (a + b)[7:0])
    );

    // Subtraction opcode drives the low 8 bits of a - b.
    check_sub_result: assert property (
        @($global_clock) (op == 2'b01) |-> (result == (a - b)[7:0])
    );

    // Multiplication opcode drives the low 8 bits of a * b.
    check_mul_result: assert property (
        @($global_clock) (op == 2'b10) |-> (result == (a * b)[7:0])
    );

    // Division opcode drives the low 8 bits of a / b when b is nonzero.
    check_div_result: assert property (
        @($global_clock) ((op == 2'b11) && (b != 8'h00)) |-> (result == (a / b)[7:0])
    );

    // Division by zero drives 0xFF for all division opcodes.
    check_div_zero_result: assert property (
        @($global_clock) ((op == 2'b11) && (b == 8'h00)) |-> (result == 8'hFF)
    );

    // Multiplication overflow clamps the result to 0xFF.
    check_mul_overflow_clamp: assert property (
        @($global_clock) ((op == 2'b10) && ((a * b) > 16'h00FF)) |-> (result == 8'hFF)
    );

    // Division overflow clamps the result to 0xFF.
    check_div_overflow_clamp: assert property (
        @($global_clock) ((op == 2'b11) && ((a / b) > 8'hFF)) |-> (result == 8'hFF)
    );

endmodule