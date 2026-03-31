module four_bit_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] S,
    input logic Cout
);

    // No RTL clock or reset; sample this combinational logic on the formal global clock.

    // Sum bit 0 matches the RTL XOR of A[0], B[0], and Cin.
    check_sum_bit0: assert property (
        @($global_clock) S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Sum bit 1 uses the carry generated from bit 0.
    check_sum_bit1: assert property (
        @($global_clock)
        S[1] == (A[1] ^ B[1] ^
                 ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin)))
    );

    // Sum bit 2 uses the carry generated from bit 1.
    check_sum_bit2: assert property (
        @($global_clock)
        S[2] == (A[2] ^ B[2] ^
                 ((A[1] & B[1]) |
                  (A[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))) |
                  (B[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin)))))
    );

    // Sum bit 3 uses the carry generated from bit 2.
    check_sum_bit3: assert property (
        @($global_clock)
        S[3] == (A[3] ^ B[3] ^
                 ((A[2] & B[2]) |
                  (A[2] & ((A[1] & B[1]) |
                           (A[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))) |
                           (B[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))))) |
                  (B[2] & ((A[1] & B[1]) |
                           (A[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))) |
                           (B[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin)))))))
    );

    // Carry-out matches the RTL carry chain from bit 3.
    check_cout: assert property (
        @($global_clock)
        Cout == ((A[3] & B[3]) |
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
                                   (B[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))))))))
    );

    // The 5-bit output vector matches the RTL full-adder result.
    check_full_adder_result: assert property (
        @($global_clock)
        {Cout, S} == ({1'b0, A} + {1'b0, B} + Cin)
    );

endmodule