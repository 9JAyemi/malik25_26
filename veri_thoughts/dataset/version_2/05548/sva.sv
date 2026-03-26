module alu_sva (
    input logic clk,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [2:0] opcode,
    input logic [7:0] out
);

    // Addition opcode drives the sum of A and B.
    check_addition: assert property (
        @(posedge clk) (opcode == 3'b000) |-> (out == (A + B))
    );

    // Subtraction opcode drives A minus B.
    check_subtraction: assert property (
        @(posedge clk) (opcode == 3'b001) |-> (out == (A - B))
    );

    // Multiplication opcode drives the product of A and B.
    check_multiplication: assert property (
        @(posedge clk) (opcode == 3'b010) |-> (out == (A * B))
    );

    // Division opcode drives A divided by B when B is nonzero.
    check_division: assert property (
        @(posedge clk) ((opcode == 3'b011) && (B != 8'h00)) |-> (out == (A / B))
    );

    // AND opcode drives the bitwise AND of A and B.
    check_bitwise_and: assert property (
        @(posedge clk) (opcode == 3'b100) |-> (out == (A & B))
    );

    // OR opcode drives the bitwise OR of A and B.
    check_bitwise_or: assert property (
        @(posedge clk) (opcode == 3'b101) |-> (out == (A | B))
    );

    // XOR opcode drives the bitwise XOR of A and B.
    check_bitwise_xor: assert property (
        @(posedge clk) (opcode == 3'b110) |-> (out == (A ^ B))
    );

    // The default opcode value drives zero.
    check_default_zero: assert property (
        @(posedge clk) (opcode == 3'b111) |-> (out == 8'h00)
    );

endmodule