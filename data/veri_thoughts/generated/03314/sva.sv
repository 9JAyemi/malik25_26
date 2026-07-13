module calculator_sva (
    input logic clk,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [1:0] opcode,
    input logic [7:0] result
);

    typedef logic [7:0] u8_t;

    // Addition opcode computes the 8-bit sum.
    check_addition_result: assert property (
        @(posedge clk) (opcode == 2'b00) |-> (result == u8_t'(A + B))
    );

    // Subtraction opcode computes the 8-bit difference.
    check_subtraction_result: assert property (
        @(posedge clk) (opcode == 2'b01) |-> (result == u8_t'(A - B))
    );

    // Multiplication opcode computes the low 8 bits of the product.
    check_multiplication_result: assert property (
        @(posedge clk) (opcode == 2'b10) |-> (result == u8_t'(A * B))
    );

    // Division by zero returns the error code 8'hFF.
    check_division_by_zero_result: assert property (
        @(posedge clk) (opcode == 2'b11 && B == 8'h00) |-> (result == 8'hFF)
    );

    // Division opcode computes the quotient when B is nonzero.
    check_division_nonzero_result: assert property (
        @(posedge clk) (opcode == 2'b11 && B != 8'h00) |-> (result == u8_t'(A / B))
    );

endmodule