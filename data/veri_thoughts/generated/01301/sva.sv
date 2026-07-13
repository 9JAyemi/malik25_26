module four_bit_adder_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S,
    input logic Cout
);
    // Final 5-bit sum must equal zero-extended A+B.
    check_sum_matches_addition: assert property (
        @(posedge CLK) {Cout, S} == ({1'b0, A} + {1'b0, B})
    );

    // LSB sum is XOR with Cin=0.
    check_s0_is_xor: assert property (
        @(posedge CLK) S[0] == (A[0] ^ B[0])
    );

    // Carry into bit1 equals A0&B0 (derived via S1 parity).
    check_carry_into_bit1: assert property (
        @(posedge CLK) (S[1] ^ A[1] ^ B[1]) == (A[0] & B[0])
    );

    // Bit1 sum equals XOR with carry from bit0.
    check_s1_is_xor_with_carry: assert property (
        @(posedge CLK) S[1] == (A[1] ^ B[1] ^ (A[0] & B[0]))
    );

    // Carry into bit2 equals (A1&B1) | ((A0&B0)&(A1^B1)).
    check_carry_into_bit2: assert property (
        @(posedge CLK) (S[2] ^ A[2] ^ B[2]) == ((A[1] & B[1]) | ((A[0] & B[0]) & (A[1] ^ B[1])))
    );

    // Bit2 sum equals XOR with computed carry into bit2.
    check_s2_is_xor_with_carry: assert property (
        @(posedge CLK) S[2] == (A[2] ^ B[2] ^ ((A[1] & B[1]) | ((A[0] & B[0]) & (A[1] ^ B[1]))))
    );

    // Carry into bit3 equals (A2&B2) | (c1&(A2^B2)) with c1 expanded.
    check_carry_into_bit3: assert property (
        @(posedge CLK) (S[3] ^ A[3] ^ B[3]) ==
            ((A[2] & B[2]) | (((A[1] & B[1]) | ((A[0] & B[0]) & (A[1] ^ B[1]))) & (A[2] ^ B[2])))
    );

    // Bit3 sum equals XOR with computed carry into bit3.
    check_s3_is_xor_with_carry: assert property (
        @(posedge CLK) S[3] == (A[3] ^ B[3] ^
            ((A[2] & B[2]) | (((A[1] & B[1]) | ((A[0] & B[0]) & (A[1] ^ B[1]))) & (A[2] ^ B[2]))))
    );

    // Cout equals (A3&B3) | (c2&(A3^B3)) with c2 expanded.
    check_cout_from_final_carry: assert property (
        @(posedge CLK) Cout ==
            ((A[3] & B[3]) | (
                ((A[2] & B[2]) | (((A[1] & B[1]) | ((A[0] & B[0]) & (A[1] ^ B[1]))) & (A[2] ^ B[2])))
                & (A[3] ^ B[3])
            ))
    );
endmodule