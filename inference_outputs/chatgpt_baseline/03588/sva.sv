module bitwise_and_sva (
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [7:0] C
);

    // Output bus must equal the bitwise AND of A and B.
    check_output_matches_bitwise_and: assert property (
        @($global_clock) C == (A & B)
    );

    // Bit 0 output must equal A[0] AND B[0].
    check_bit0_and: assert property (
        @($global_clock) C[0] == (A[0] & B[0])
    );

    // Bit 1 output must equal A[1] AND B[1].
    check_bit1_and: assert property (
        @($global_clock) C[1] == (A[1] & B[1])
    );

    // Bit 2 output must equal A[2] AND B[2].
    check_bit2_and: assert property (
        @($global_clock) C[2] == (A[2] & B[2])
    );

    // Bit 3 output must equal A[3] AND B[3].
    check_bit3_and: assert property (
        @($global_clock) C[3] == (A[3] & B[3])
    );

    // Bit 4 output must equal A[4] AND B[4].
    check_bit4_and: assert property (
        @($global_clock) C[4] == (A[4] & B[4])
    );

    // Bit 5 output must equal A[5] AND B[5].
    check_bit5_and: assert property (
        @($global_clock) C[5] == (A[5] & B[5])
    );

    // Bit 6 output must equal A[6] AND B[6].
    check_bit6_and: assert property (
        @($global_clock) C[6] == (A[6] & B[6])
    );

    // Bit 7 output must equal A[7] AND B[7].
    check_bit7_and: assert property (
        @($global_clock) C[7] == (A[7] & B[7])
    );

endmodule