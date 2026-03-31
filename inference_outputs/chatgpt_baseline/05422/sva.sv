module calculator_sva(
    input logic clk,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [1:0] op,
    input logic [7:0] result
);

    // Addition opcode returns A + B, truncated to 8 bits.
    check_add_operation: assert property (
        @(posedge clk) (op == 2'b00) |-> (result == ((A + B) & 8'hff))
    );

    // Subtraction opcode returns A - B, truncated to 8 bits.
    check_sub_operation: assert property (
        @(posedge clk) (op == 2'b01) |-> (result == ((A - B) & 8'hff))
    );

    // Multiplication opcode returns A * B, truncated to 8 bits.
    check_mul_operation: assert property (
        @(posedge clk) (op == 2'b10) |-> (result == ((A * B) & 8'hff))
    );

    // Division by zero forces the result to zero.
    check_div_by_zero: assert property (
        @(posedge clk) (op == 2'b11 && B == 8'h00) |-> (result == 8'h00)
    );

    // Division opcode returns A / B when B is nonzero.
    check_div_operation: assert property (
        @(posedge clk) (op == 2'b11 && B != 8'h00) |-> (result == (A / B))
    );

endmodule