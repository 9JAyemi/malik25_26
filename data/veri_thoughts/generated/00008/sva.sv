module calculator_sva (
    input logic clk,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [1:0] op,
    input logic [7:0] Y
);

    // Addition opcode drives Y with the 8-bit sum.
    check_addition_result: assert property (
        @(posedge clk)
        (op === 2'b00) |-> (Y === 8'(A + B))
    );

    // Subtraction opcode drives Y with the 8-bit difference.
    check_subtraction_result: assert property (
        @(posedge clk)
        (op === 2'b01) |-> (Y === 8'(A - B))
    );

    // Multiplication opcode drives Y with the low 8 bits of the product.
    check_multiplication_result: assert property (
        @(posedge clk)
        (op === 2'b10) |-> (Y === 8'(A * B))
    );

    // Division opcode drives Y with the quotient when the divisor is known and nonzero.
    check_division_result: assert property (
        @(posedge clk)
        ((op === 2'b11) && !$isunknown(B) && (B != 8'h00)) |-> (Y === 8'(A / B))
    );

endmodule