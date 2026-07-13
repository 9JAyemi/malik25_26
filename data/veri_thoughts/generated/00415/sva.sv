module calculator_sva (
    input logic clk,
    input logic [2:0] opcode,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [7:0] result
);

    // Addition opcode drives the 8-bit sum.
    check_addition_result: assert property (
        @(posedge clk) (opcode == 3'b000) |-> ({8'h00, result} == ((A + B) & 16'h00FF))
    );

    // Subtraction opcode drives the 8-bit difference.
    check_subtraction_result: assert property (
        @(posedge clk) (opcode == 3'b001) |-> ({8'h00, result} == ((A - B) & 16'h00FF))
    );

    // Multiplication opcode drives the low 8 bits of the product.
    check_multiplication_result: assert property (
        @(posedge clk) (opcode == 3'b010) |-> ({8'h00, result} == ((A * B) & 16'h00FF))
    );

    // Division opcode drives the quotient when the divisor is nonzero.
    check_division_result: assert property (
        @(posedge clk) (opcode == 3'b011 && B != 8'h00) |-> ({8'h00, result} == ((A / B) & 16'h00FF))
    );

    // Invalid opcodes drive result to zero.
    check_default_result_zero: assert property (
        @(posedge clk) (opcode[2] == 1'b1) |-> (result == 8'h00)
    );

endmodule