module ripple_carry_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic CI,
    input logic [3:0] S,
    input logic CO
);

    // S[0] is the XOR of A[0], B[0], and CI.
    check_sum_bit0_xor: assert property (
        @($global_clock) S[0] == (A[0] ^ B[0] ^ CI)
    );

    // S[1] is the XOR of A[1], B[1], and the carry from bit 0.
    check_sum_bit1_xor: assert property (
        @($global_clock) S[1] == (A[1] ^ B[1] ^ (A[0] & B[0] | B[0] & CI | A[0] & CI))
    );

    // S[2] is the XOR of A[2], B[2], and the carry from bit 1.
    check_sum_bit2_xor: assert property (
        @($global_clock) S[2] == (A[2] ^ B[2] ^ (
            A[1] & B[1] | B[1] & (A[0] & B[0] | B[0] & CI | A[0] & CI) | A[1] & (A[0] & B[0] | B[0] & CI | A[0] & CI)
        ))
    );

    // S[3] is the XOR of A[3], B[3], and the carry from bit 2.
    check_sum_bit3_xor: assert property (
        @($global_clock) S[3] == (A[3] ^ B[3] ^ (
            A[2] & B[2] | B[2] & (
                A[1] & B[1] | B[1] & (A[0] & B[0] | B[0] & CI | A[0] & CI) | A[1] & (A[0] & B[0] | B[0] & CI | A[0] & CI)
            ) | A[2] & (
                A[1] & B[1] | B[1] & (A[0] & B[0] | B[0] & CI | A[0] & CI) | A[1] & (A[0] & B[0] | B[0] & CI | A[0] & CI)
            )
        ))
    );

    // CO is the carry out from the final full-adder stage.
    check_carry_out: assert property (
        @($global_clock) CO == (
            A[3] & B[3] | B[3] & (
                A[2] & B[2] | B[2] & (
                    A[1] & B[1] | B[1] & (A[0] & B[0] | B[0] & CI | A[0] & CI) | A[1] & (A[0] & B[0] | B[0] & CI | A[0] & CI)
                ) | A[2] & (
                    A[1] & B[1] | B[1] & (A[0] & B[0] | B[0] & CI | A[0] & CI) | A[1] & (A[0] & B[0] | B[0] & CI | A[0] & CI)
                )
            ) | A[3] & (
                A[2] & B[2] | B[2] & (
                    A[1] & B[1] | B[1] & (A[0] & B[0] | B[0] & CI | A[0] & CI) | A[1] & (A[0] & B[0] | B[0] & CI | A[0] & CI)
                ) | A[2] & (
                    A[1] & B[1] | B[1] & (A[0] & B[0] | B[0] & CI | A[0] & CI) | A[1] & (A[0] & B[0] | B[0] & CI | A[0] & CI)
                )
            )
        )
    );

    // The 5-bit output is the sum of A, B, and CI.
    check_total_sum: assert property (
        @($global_clock) {CO, S} == ({1'b0, A} + {1'b0, B} + CI)
    );

endmodule