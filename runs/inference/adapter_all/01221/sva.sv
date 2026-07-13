module alu_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [2:0] opcode,
    input logic [3:0] out,
    input logic zero
);

    // Opcode 000 selects add.
    check_add_result: assert property (
        @($global_clock) (opcode == 3'b000) |-> (out == (A + B))
    );

    // Opcode 001 selects subtract.
    check_subtract_result: assert property (
        @($global_clock) (opcode == 3'b001) |-> (out == (A - B))
    );

    // Opcode 010 selects bitwise AND.
    check_and_result: assert property (
        @($global_clock) (opcode == 3'b010) |-> (out == (A & B))
    );

    // Opcode 011 selects bitwise OR.
    check_or_result: assert property (
        @($global_clock) (opcode == 3'b011) |-> (out == (A | B))
    );

    // Opcode 100 selects bitwise XOR.
    check_xor_result: assert property (
        @($global_clock) (opcode == 3'b100) |-> (out == (A ^ B))
    );

    // Opcode 101 selects shift left by 1.
    check_shift_left_result: assert property (
        @($global_clock) (opcode == 3'b101) |-> (out == (A << 1))
    );

    // Opcode 110 selects shift right by 1.
    check_shift_right_result: assert property (
        @($global_clock) (opcode == 3'b110) |-> (out == (A >> 1))
    );

    // Opcode 111 selects bitwise NOT of A.
    check_not_result: assert property (
        @($global_clock) (opcode == 3'b111) |-> (out == (~A))
    );

    // Zero flag is asserted when the output is zero.
    check_zero_flag_asserted: assert property (
        @($global_clock) (out == 4'b0000) |-> (zero == 1'b1)
    );

    // Zero flag is deasserted when the output is nonzero.
    check_zero_flag_deasserted: assert property (
        @($global_clock) (out != 4'b0000) |-> (zero == 1'b0)
    );

endmodule