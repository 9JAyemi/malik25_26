module binary_to_gray_sva (
    input logic [3:0] A,
    input logic [3:0] G
);

    // G[3] is a direct copy of A[3].
    check_gray_bit3_passthrough: assert property (
        @($global_clock) G[3] == A[3]
    );

    // G[2] is the XOR of A[3] and A[2].
    check_gray_bit2_xor: assert property (
        @($global_clock) G[2] == (A[3] ^ A[2])
    );

    // G[1] is the XOR of A[2] and A[1].
    check_gray_bit1_xor: assert property (
        @($global_clock) G[1] == (A[2] ^ A[1])
    );

    // G[0] is the XOR of A[1] and A[0].
    check_gray_bit0_xor: assert property (
        @($global_clock) G[0] == (A[1] ^ A[0])
    );

    // The full Gray output matches the implemented conversion.
    check_gray_vector_mapping: assert property (
        @($global_clock) G == {A[3], (A[3] ^ A[2]), (A[2] ^ A[1]), (A[1] ^ A[0])}
    );

endmodule