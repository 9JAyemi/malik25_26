module alu_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [2:0] opcode,
    input logic [3:0] out,
    input logic zero
);

    // Opcode 000 selects the 4-bit sum of A and B.
    check_add_result: assert property (
        @($global_clock) (opcode == 3'b000) |-> (out == (A + B))
    );

    // Opcode 001 selects the 4-bit difference of A and B.
    check_sub_result: assert property (
        @($global_clock) (opcode == 3'b001) |-> (out == (A - B))
    );

    // Opcode 010 selects the bitwise AND of A and B.
    check_and_result: assert property (
        @($global_clock) (opcode == 3'b010) |-> (out == (A & B))
    );

    // Opcode 011 selects the bitwise OR of A and B.
    check_or_result: assert property (
        @($global_clock) (opcode == 3'b011) |-> (out == (A | B))
    );

    // Opcode 100 selects the bitwise XOR of A and B.
    check_xor_result: assert property (
        @($global_clock) (opcode == 3'b100) |-> (out == (A ^ B))
    );

    // Opcode 101 selects the logical left shift of A by one.
    check_shift_left_result: assert property (
        @($global_clock) (opcode == 3'b101) |-> (out == (A << 1))
    );

    // Opcode 110 selects the logical right shift of A by one.
    check_shift_right_result: assert property (
        @($global_clock) (opcode == 3'b110) |-> (out == (A >> 1))
    );

    // Opcode 111 selects the bitwise NOT of A.
    check_not_result: assert property (
        @($global_clock) (opcode == 3'b111) |-> (out == (~A))
    );

    // Zero is asserted exactly when the computed output is zero.
    check_zero_flag: assert property (
        @($global_clock) (zero == (out == 4'b0000))
    );

endmodule