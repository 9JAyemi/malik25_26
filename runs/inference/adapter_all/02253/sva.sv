module alu_sva (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [2:0] op,
    input logic [3:0] out
);

    // Addition opcode drives the sum of a and b.
    check_add_result: assert property (
        @($global_clock) (op == 3'b000) |-> (out == (a + b))
    );

    // Subtraction opcode drives the difference of a and b.
    check_sub_result: assert property (
        @($global_clock) (op == 3'b001) |-> (out == (a - b))
    );

    // AND opcode drives the bitwise AND of a and b.
    check_and_result: assert property (
        @($global_clock) (op == 3'b010) |-> (out == (a & b))
    );

    // OR opcode drives the bitwise OR of a and b.
    check_or_result: assert property (
        @($global_clock) (op == 3'b011) |-> (out == (a | b))
    );

    // XOR opcode drives the bitwise XOR of a and b.
    check_xor_result: assert property (
        @($global_clock) (op == 3'b100) |-> (out == (a ^ b))
    );

    // Shift-left opcode drives the left-shifted value of a.
    check_shift_left_result: assert property (
        @($global_clock) (op == 3'b101) |-> (out == {a[2:0], 1'b0})
    );

    // Unsupported opcodes drive zero.
    check_default_zero: assert property (
        @($global_clock) (op inside {3'b110, 3'b111}) |-> (out == 4'b0000)
    );

endmodule