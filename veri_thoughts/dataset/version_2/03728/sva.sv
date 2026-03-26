module top_module_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [2:0] OP,
    input logic [3:0] Y
);

    // No RTL clock or reset exists; clk is only a sampling clock for these checks.

    // Y must follow the top-level opcode decode.
    check_output_decode: assert property (
        @(posedge clk)
        Y == ((OP == 3'b000) ? (A + B) :
              (OP == 3'b001) ? (A + B) :
              (OP == 3'b010) ? (A & B) :
              (OP == 3'b011) ? (A | B) :
              (OP == 3'b100) ? (A ^ B) :
                               4'b0000)
    );

    // Opcodes 000 and 001 select the adder result.
    check_add_opcodes: assert property (
        @(posedge clk) ((OP == 3'b000) || (OP == 3'b001)) |-> (Y == (A + B))
    );

    // Opcode 010 selects bitwise AND.
    check_and_opcode: assert property (
        @(posedge clk) (OP == 3'b010) |-> (Y == (A & B))
    );

    // Opcode 011 selects bitwise OR.
    check_or_opcode: assert property (
        @(posedge clk) (OP == 3'b011) |-> (Y == (A | B))
    );

    // Opcode 100 selects bitwise XOR.
    check_xor_opcode: assert property (
        @(posedge clk) (OP == 3'b100) |-> (Y == (A ^ B))
    );

    // Unused opcodes drive zero.
    check_default_zero_opcodes: assert property (
        @(posedge clk) ((OP == 3'b101) || (OP == 3'b110) || (OP == 3'b111)) |-> (Y == 4'b0000)
    );

    // Stable inputs must produce a stable output.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(A) && $stable(B) && $stable(OP)) |-> $stable(Y)
    );

endmodule