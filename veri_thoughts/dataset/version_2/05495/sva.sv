module xor_8bit_sva (
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [7:0] Z
);

    // Z must always equal A XOR B.
    check_xor_function: assert property (
        @($global_clock) Z == (A ^ B)
    );

    // Bit 0 of Z must be A[0] XOR B[0].
    check_bit0_xor: assert property (
        @($global_clock) Z[0] == (A[0] ^ B[0])
    );

    // Bit 1 of Z must be A[1] XOR B[1].
    check_bit1_xor: assert property (
        @($global_clock) Z[1] == (A[1] ^ B[1])
    );

    // Bit 2 of Z must be A[2] XOR B[2].
    check_bit2_xor: assert property (
        @($global_clock) Z[2] == (A[2] ^ B[2])
    );

    // Bit 3 of Z must be A[3] XOR B[3].
    check_bit3_xor: assert property (
        @($global_clock) Z[3] == (A[3] ^ B[3])
    );

    // Bit 4 of Z must be A[4] XOR B[4].
    check_bit4_xor: assert property (
        @($global_clock) Z[4] == (A[4] ^ B[4])
    );

    // Bit 5 of Z must be A[5] XOR B[5].
    check_bit5_xor: assert property (
        @($global_clock) Z[5] == (A[5] ^ B[5])
    );

    // Bit 6 of Z must be A[6] XOR B[6].
    check_bit6_xor: assert property (
        @($global_clock) Z[6] == (A[6] ^ B[6])
    );

    // Bit 7 of Z must be A[7] XOR B[7].
    check_bit7_xor: assert property (
        @($global_clock) Z[7] == (A[7] ^ B[7])
    );

    // Equal inputs must produce zero.
    check_equal_inputs_zero: assert property (
        @($global_clock) (A == B) |-> (Z == 8'h00)
    );

    // Zero on A must pass B through to Z.
    check_a_zero_passthrough: assert property (
        @($global_clock) (A == 8'h00) |-> (Z == B)
    );

    // Zero on B must pass A through to Z.
    check_b_zero_passthrough: assert property (
        @($global_clock) (B == 8'h00) |-> (Z == A)
    );

    // All ones on A must invert B.
    check_a_all_ones_inverts_b: assert property (
        @($global_clock) (A == 8'hFF) |-> (Z == ~B)
    );

    // All ones on B must invert A.
    check_b_all_ones_inverts_a: assert property (
        @($global_clock) (B == 8'hFF) |-> (Z == ~A)
    );

endmodule