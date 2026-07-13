module XOR_4bit_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] Z
);

    // Z must equal the bitwise XOR of A and B.
    check_vector_xor_function: assert property (
        @($global_clock) Z == (A ^ B)
    );

    // Z[0] must be A[0] XOR B[0].
    check_bit0_xor: assert property (
        @($global_clock) Z[0] == (A[0] ^ B[0])
    );

    // Z[1] must be A[1] XOR B[1].
    check_bit1_xor: assert property (
        @($global_clock) Z[1] == (A[1] ^ B[1])
    );

    // Z[2] must be A[2] XOR B[2].
    check_bit2_xor: assert property (
        @($global_clock) Z[2] == (A[2] ^ B[2])
    );

    // Z[3] must be A[3] XOR B[3].
    check_bit3_xor: assert property (
        @($global_clock) Z[3] == (A[3] ^ B[3])
    );

    // Equal inputs must produce a zero output.
    check_equal_inputs_zero_output: assert property (
        @($global_clock) (A == B) |-> (Z == 4'h0)
    );

    // A zero output must mean the inputs are equal.
    check_zero_output_equal_inputs: assert property (
        @($global_clock) (Z == 4'h0) |-> (A == B)
    );

    // If A is zero, Z must pass through B.
    check_a_zero_passthrough_b: assert property (
        @($global_clock) (A == 4'h0) |-> (Z == B)
    );

    // If B is zero, Z must pass through A.
    check_b_zero_passthrough_a: assert property (
        @($global_clock) (B == 4'h0) |-> (Z == A)
    );

    // An all-ones output must mean the inputs are bitwise complements.
    check_all_ones_output_means_complements: assert property (
        @($global_clock) (Z == 4'hF) |-> (A == ~B)
    );

endmodule