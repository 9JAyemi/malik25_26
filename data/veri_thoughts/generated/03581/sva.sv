module adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] sum
);

    // sum must equal the 4-bit addition of A and B.
    check_sum_matches_addition: assert property (
        @($global_clock) sum == (A + B)
    );

    // Bit 0 must be the XOR of the input LSBs.
    check_sum_bit0: assert property (
        @($global_clock) sum[0] == (A[0] ^ B[0])
    );

    // Bit 1 must include the carry from bit 0.
    check_sum_bit1: assert property (
        @($global_clock) sum[1] == (A[1] ^ B[1] ^ (A[0] & B[0]))
    );

    // Bit 2 must include the carry from bit 1.
    check_sum_bit2: assert property (
        @($global_clock) sum[2] == (A[2] ^ B[2] ^
            ((A[1] & B[1]) | ((A[1] ^ B[1]) & (A[0] & B[0])))
        )
    );

    // Bit 3 must include the carry from bit 2.
    check_sum_bit3: assert property (
        @($global_clock) sum[3] == (A[3] ^ B[3] ^
            ((A[2] & B[2]) | ((A[2] ^ B[2]) &
            ((A[1] & B[1]) | ((A[1] ^ B[1]) & (A[0] & B[0])))))
        )
    );

    // Zero on A must pass B through to sum.
    check_zero_a_passthrough: assert property (
        @($global_clock) (A == 4'h0) |-> (sum == B)
    );

    // Zero on B must pass A through to sum.
    check_zero_b_passthrough: assert property (
        @($global_clock) (B == 4'h0) |-> (sum == A)
    );

endmodule