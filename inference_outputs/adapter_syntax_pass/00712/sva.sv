module adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] C
);

    // C must always equal the 4-bit sum of A and B.
    check_sum_matches_inputs: assert property (
        @($global_clock) C == (A + B)
    );

    // Adding zero on A must pass B through to C.
    check_zero_a_passthrough: assert property (
        @($global_clock) (A == 4'h0) |-> (C == B)
    );

    // Adding zero on B must pass A through to C.
    check_zero_b_passthrough: assert property (
        @($global_clock) (B == 4'h0) |-> (C == A)
    );

    // The least-significant sum bit must be the XOR of the input LSBs.
    check_lsb_sum: assert property (
        @($global_clock) C[0] == (A[0] ^ B[0])
    );

    // The full 4-bit result must never exceed 4 bits.
    check_output_range: assert property (
        @($global_clock) C <= 4'hF
    );

endmodule