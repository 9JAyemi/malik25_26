module adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S,
    input logic C_out
);

    // S[0] is A[0] XOR B[0] because the carry-in is tied low.
    check_sum_bit0_xor: assert property (
        @($global_clock) S[0] == (A[0] ^ B[0])
    );

    // S[1] is A[1] XOR B[1] XOR the carry from bit 0.
    check_sum_bit1_with_carry0: assert property (
        @($global_clock) S[1] == (A[1] ^ B[1] ^ (A[0] & B[0]))
    );

    // S[2] is A[2] XOR B[2] XOR the carry from bit 1.
    check_sum_bit2_with_carry1: assert property (
        @($global_clock)
        S[2] == (A[2] ^ B[2] ^
                 ((A[1] & B[1]) |
                  (A[1] & (A[0] & B[0])) |
                  (B[1] & (A[0] & B[0]))))
    );

    // S[3] is A[3] XOR B[3] XOR the carry from bit 2.
    check_sum_bit3_with_carry2: assert property (
        @($global_clock)
        S[3] == (A[3] ^ B[3] ^
                 ((A[2] & B[2]) |
                  (A[2] & ((A[1] & B[1]) |
                           (A[1] & (A[0] & B[0])) |
                           (B[1] & (A[0] & B[0])))) |
                  (B[2] & ((A[1] & B[1]) |
                           (A[1] & (A[0] & B[0])) |
                           (B[1] & (A[0] & B[0])))))))
    );

    // C_out is the carry out from the MSB stage.
    check_cout_from_bit3: assert property (
        @($global_clock)
        C_out == ((A[3] & B[3]) |
                  (A[3] & ((A[2] & B[2]) |
                           (A[2] & ((A[1] & B[1]) |
                                    (A[1] & (A[0] & B[0])) |
                                    (B[1] & (A[0] & B[0])))) |
                           (B[2] & ((A[1] & B[1]) |
                                    (A[1] & (A[0] & B[0])) |
                                    (B[1] & (A[0] & B[0])))))) |
                  (B[3] & ((A[2] & B[2]) |
                           (A[2] & ((A[1] & B[1]) |
                                    (A[1] & (A[0] & B[0])) |
                                    (B[1] & (A[0] & B[0])))) |
                           (B[2] & ((A[1] & B[1]) |
                                    (A[1] & (A[0] & B[0])) |
                                    (B[1] & (A[0] & B[0])))))))
    );

    // The full output matches the 5-bit addition of A and B.
    check_full_addition: assert property (
        @($global_clock) {C_out, S} == ({1'b0, A} + {1'b0, B})
    );

endmodule