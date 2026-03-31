module four_bit_adder_sva (
    input logic [3:0] S,
    input logic       CO,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       CI
);

    // S[0] matches the full-adder XOR of A[0], B[0], and CI.
    check_sum_bit0: assert property (
        @($global_clock) S[0] == (A[0] ^ B[0] ^ CI)
    );

    // S[1] matches the full-adder XOR of A[1], B[1], and the carry from bit 0.
    check_sum_bit1: assert property (
        @($global_clock)
        S[1] == (A[1] ^ B[1] ^ ((A[0] & B[0]) | (A[0] & CI) | (B[0] & CI)))
    );

    // S[2] matches the full-adder XOR of A[2], B[2], and the carry from bit 1.
    check_sum_bit2: assert property (
        @($global_clock)
        S[2] == (A[2] ^ B[2] ^ (
            (A[1] & B[1]) |
            (A[1] & ((A[0] & B[0]) | (A[0] & CI) | (B[0] & CI))) |
            (B[1] & ((A[0] & B[0]) | (A[0] & CI) | (B[0] & CI)))
        ))
    );

    // S[3] matches the full-adder XOR of A[3], B[3], and the carry from bit 2.
    check_sum_bit3: assert property (
        @($global_clock)
        S[3] == (A[3] ^ B[3] ^ (
            (A[2] & B[2]) |
            (A[2] & (
                (A[1] & B[1]) |
                (A[1] & ((A[0] & B[0]) | (A[0] & CI) | (B[0] & CI))) |
                (B[1] & ((A[0] & B[0]) | (A[0] & CI) | (B[0] & CI)))
            )) |
            (B[2] & (
                (A[1] & B[1]) |
                (A[1] & ((A[0] & B[0]) | (A[0] & CI) | (B[0] & CI))) |
                (B[1] & ((A[0] & B[0]) | (A[0] & CI) | (B[0] & CI)))
            ))
        ))
    );

    // CO matches the full-adder carry-out of A[3], B[3], and the carry from bit 2.
    check_carry_out: assert property (
        @($global_clock)
        CO == (
            (A[3] & B[3]) |
            (A[3] & (
                (A[2] & B[2]) |
                (A[2] & (
                    (A[1] & B[1]) |
                    (A[1] & ((A[0] & B[0]) | (A[0] & CI) | (B[0] & CI))) |
                    (B[1] & ((A[0] & B[0]) | (A[0] & CI) | (B[0] & CI)))
                )) |
                (B[2] & (
                    (A[1] & B[1]) |
                    (A[1] & ((A[0] & B[0]) | (A[0] & CI) | (B[0] & CI))) |
                    (B[1] & ((A[0] & B[0]) | (A[0] & CI) | (B[0] & CI)))
                ))
            )) |
            (B[3] & (
                (A[2] & B[2]) |
                (A[2] & (
                    (A[1] & B[1]) |
                    (A[1] & ((A[0] & B[0]) | (A[0] & CI) | (B[0] & CI))) |
                    (B[1] & ((A[0] & B[0]) | (A[0] & CI) | (B[0] & CI)))
                )) |
                (B[2] & (
                    (A[1] & B[1]) |
                    (A[1] & ((A[0] & B[0]) | (A[0] & CI) | (B[0] & CI))) |
                    (B[1] & ((A[0] & B[0]) | (A[0] & CI) | (B[0] & CI)))
                ))
            ))
        )
    );

endmodule