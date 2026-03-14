module RCA_N4_17_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Ci,
    input logic [3:0] S,
    input logic Co
);
    // Sum and carry must equal 5-bit addition of A+B+Ci.
    check_sum_matches_adder: assert property (
        @(posedge CLK) {Co, S} == ({1'b0, A} + {1'b0, B} + Ci)
    );

    // Carry-out equals MSB of 5-bit sum.
    check_carry_is_msb_of_sum: assert property (
        @(posedge CLK) Co == (({1'b0, A} + {1'b0, B} + Ci) >= 5'd16)
    );

    // Bit 0 sum is XOR of A[0], B[0], Ci.
    check_s0_xor: assert property (
        @(posedge CLK) S[0] == (A[0] ^ B[0] ^ Ci)
    );

    // Bit 1 sum is XOR of A[1], B[1], and c1.
    check_s1_xor: assert property (
        @(posedge CLK) S[1] == (A[1] ^ B[1] ^ ( (A[0] & B[0]) | (A[0] & Ci) | (B[0] & Ci) ))
    );

    // Bit 2 sum is XOR of A[2], B[2], and c2.
    check_s2_xor: assert property (
        @(posedge CLK) S[2] == (
            A[2] ^ B[2] ^
            (
                (A[1] & B[1]) |
                (A[1] & ( (A[0] & B[0]) | (A[0] & Ci) | (B[0] & Ci) )) |
                (B[1] & ( (A[0] & B[0]) | (A[0] & Ci) | (B[0] & Ci) ))
            )
        )
    );

    // Bit 3 sum is XOR of A[3], B[3], and c3.
    check_s3_xor: assert property (
        @(posedge CLK) S[3] == (
            A[3] ^ B[3] ^
            (
                (A[2] & B[2]) |
                (A[2] &
                    (
                        (A[1] & B[1]) |
                        (A[1] & ( (A[0] & B[0]) | (A[0] & Ci) | (B[0] & Ci) )) |
                        (B[1] & ( (A[0] & B[0]) | (A[0] & Ci) | (B[0] & Ci) ))
                    )
                ) |
                (B[2] &
                    (
                        (A[1] & B[1]) |
                        (A[1] & ( (A[0] & B[0]) | (A[0] & Ci) | (B[0] & Ci) )) |
                        (B[1] & ( (A[0] & B[0]) | (A[0] & Ci) | (B[0] & Ci) ))
                    )
                )
            )
        )
    );

    // Carry-out equals chained majority over bit 3 with c3.
    check_co_chained_majority: assert property (
        @(posedge CLK) Co == (
            (A[3] & B[3]) |
            (A[3] &
                (
                    (A[2] & B[2]) |
                    (A[2] &
                        (
                            (A[1] & B[1]) |
                            (A[1] & ( (A[0] & B[0]) | (A[0] & Ci) | (B[0] & Ci) )) |
                            (B[1] & ( (A[0] & B[0]) | (A[0] & Ci) | (B[0] & Ci) ))
                        )
                    ) |
                    (B[2] &
                        (
                            (A[1] & B[1]) |
                            (A[1] & ( (A[0] & B[0]) | (A[0] & Ci) | (B[0] & Ci) )) |
                            (B[1] & ( (A[0] & B[0]) | (A[0] & Ci) | (B[0] & Ci) ))
                        )
                    )
                )
            ) |
            (B[3] &
                (
                    (A[2] & B[2]) |
                    (A[2] &
                        (
                            (A[1] & B[1]) |
                            (A[1] & ( (A[0] & B[0]) | (A[0] & Ci) | (B[0] & Ci) )) |
                            (B[1] & ( (A[0] & B[0]) | (A[0] & Ci) | (B[0] & Ci) ))
                        )
                    ) |
                    (B[2] &
                        (
                            (A[1] & B[1]) |
                            (A[1] & ( (A[0] & B[0]) | (A[0] & Ci) | (B[0] & Ci) )) |
                            (B[1] & ( (A[0] & B[0]) | (A[0] & Ci) | (B[0] & Ci) ))
                        )
                    )
                )
            )
        )
    );

    // When B==0 and Ci==0, output equals A with zero carry.
    check_propagate_A_when_B_zero: assert property (
        @(posedge CLK) ((B == 4'b0000) && (Ci == 1'b0)) |-> ({Co, S} == {1'b0, A})
    );

    // When A==0 and Ci==0, output equals B with zero carry.
    check_propagate_B_when_A_zero: assert property (
        @(posedge CLK) ((A == 4'b0000) && (Ci == 1'b0)) |-> ({Co, S} == {1'b0, B})
    );

    // Outputs remain stable if inputs are stable across cycles.
    check_stability_when_inputs_stable: assert property (
        @(posedge CLK) ($stable(A) && $stable(B) && $stable(Ci)) |-> ($stable(S) && $stable(Co))
    );
endmodule