module calculator_sva(
    input logic clk,
    input logic [7:0] input1,
    input logic [7:0] input2,
    input logic [2:0] opcode,
    input logic [7:0] result
);

    // No clock or reset in RTL; sample combinational behavior on clk.

    // Opcode 000 performs 8-bit addition.
    check_add_result: assert property (
        @(posedge clk) (opcode == 3'b000) |-> (result == ((input1 + input2)[7:0]))
    );

    // Opcode 001 performs 8-bit subtraction.
    check_sub_result: assert property (
        @(posedge clk) (opcode == 3'b001) |-> (result == ((input1 - input2)[7:0]))
    );

    // Opcode 010 performs 8-bit truncated multiplication.
    check_mul_result: assert property (
        @(posedge clk) (opcode == 3'b010) |-> (result == ((input1 * input2)[7:0]))
    );

    // Opcode 011 performs division when the divisor is nonzero.
    check_div_result: assert property (
        @(posedge clk) (opcode == 3'b011 && input2 != 8'h00) |-> (result == (input1 / input2))
    );

    // Opcode 100 performs bitwise AND.
    check_and_result: assert property (
        @(posedge clk) (opcode == 3'b100) |-> (result == (input1 & input2))
    );

    // Opcode 101 performs bitwise OR.
    check_or_result: assert property (
        @(posedge clk) (opcode == 3'b101) |-> (result == (input1 | input2))
    );

    // Opcode 110 performs bitwise XOR.
    check_xor_result: assert property (
        @(posedge clk) (opcode == 3'b110) |-> (result == (input1 ^ input2))
    );

    // Opcode 111 performs bitwise inversion of input1.
    check_not_result: assert property (
        @(posedge clk) (opcode == 3'b111) |-> (result == (~input1))
    );

endmodule