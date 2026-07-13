module four_bit_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       Ci,
    input logic [3:0] S,
    input logic       Co
);

    // No RTL clock or reset; sample this combinational logic on the formal global clock.

    // The 5-bit output must equal A + B + Ci.
    check_total_sum: assert property (
        @($global_clock) {Co, S} == ({1'b0, A} + {1'b0, B} + {4'b0000, Ci})
    );

    // Bit 0 sum must match the first full adder.
    check_bit0_sum: assert property (
        @($global_clock) S[0] == (A[0] ^ B[0] ^ Ci)
    );

    // Bit 1 sum must use the carry from bit 0.
    check_bit1_sum: assert property (
        @($global_clock) S[1] == (A[1] ^ B[1] ^ ((A[0] & B[0]) | ((A[0] ^ B[0]) & Ci)))
    );

    // Bit 2 sum must use the carry from bit 1.
    check_bit2_sum: assert property (
        @($global_clock) S[2] == (A[2] ^ B[2] ^ ((A[1] & B[1]) | ((A[1] ^ B[1]) & ((A[0] & B[0]) | ((A[0] ^ B[0]) & Ci))))))
    );

    // Bit 3 sum must use the carry from bit 2.
    check_bit3_sum: assert property (
        @($global_clock) S[3] == (A[3] ^ B[3] ^ ((A[2] & B[2]) | ((A[2] ^ B[2]) & ((A[1] & B[1]) | ((A[1] ^ B[1]) & ((A[0] & B[0]) | ((A[0] ^ B[0]) & Ci))))))))
    );

    // Carry out must match the final full adder carry.
    check_carry_out: assert property (
        @($global_clock) Co == ((A[3] & B[3]) | ((A[3] ^ B[3]) & ((A[2] & B[2]) | ((A[2] ^ B[2]) & ((A[1] & B[1]) | ((A[1] ^ B[1]) & ((A[0] & B[0]) | ((A[0] ^ B[0]) & Ci)))))))))
    );

endmodule