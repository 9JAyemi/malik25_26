module ripple_carry_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       Cin,
    input logic [3:0] Sum,
    input logic       Cout
);

    // Sum[0] is the XOR of A[0], B[0], and Cin.
    check_sum_bit0_xor: assert property (
        @($global_clock) Sum[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Sum[1] is the XOR of A[1], B[1], and the carry from bit 0.
    check_sum_bit1_xor_with_carry0: assert property (
        @($global_clock) Sum[1] == (A[1] ^ B[1] ^ ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin)))
    );

    // Sum[2] is the XOR of A[2], B[2], and the carry from bit 1.
    check_sum_bit2_xor_with_carry1: assert property (
        @($global_clock) Sum[2] == (A[2] ^ B[2] ^
            ((A[1] & B[1]) |
             (A[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))) |
             (B[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin)))))
    );

    // Sum[3] is the XOR of A[3], B[3], and the carry from bit 2.
    check_sum_bit3_xor_with_carry2: assert property (
        @($global_clock) Sum[3] == (A[3] ^ B[3] ^
            ((A[2] & B[2]) |
             (A[2] & ((A[1] & B[1]) |
                      (A[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))) |
                      (B[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))))) |
             (B[2] & ((A[1] & B[1]) |
                      (A[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))) |
                      (B[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin)))))))
    );

    // Cout is the carry out from the final full adder.
    check_cout_from_bit3: assert property (
        @($global_clock) Cout == ((A[3] & B[3]) |
                                  (A[3] & ((A[2] & B[2]) |
                                           (A[2] & ((A[1] & B[1]) |
                                                    (A[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))) |
                                                    (B[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))))) |
                                           (B[2] & ((A[1] & B[1]) |
                                                    (A[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))) |
                                                    (B[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))))))) |
                                  (B[3] & ((A[2] & B[2]) |
                                           (A[2] & ((A[1] & B[1]) |
                                                    (A[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))) |
                                                    (B[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))))) |
                                           (B[2] & ((A[1] & B[1]) |
                                                    (A[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))) |
                                                    (B[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin)))))))))
    );

    // The 5-bit output is the sum of A, B, and Cin.
    check_full_sum_matches_inputs: assert property (
        @($global_clock) {Cout, Sum} == ({1'b0, A} + {1'b0, B} + {4'b0000, Cin})
    );

endmodule