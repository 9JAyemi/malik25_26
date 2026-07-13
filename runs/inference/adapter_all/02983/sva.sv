module adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S,
    input logic C_out
);

    // No RTL clock or reset; sample combinational behavior on the formal global clock.

    // S[0] matches the RTL XOR with the first carry constant.
    check_sum_bit0: assert property (
        @($global_clock) S[0] == (A[0] ^ B[0] ^ 1'b0)
    );

    // S[1] matches the RTL XOR with the carry generated from bit 0.
    check_sum_bit1: assert property (
        @($global_clock) S[1] == (A[1] ^ B[1] ^ ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0)))
    );

    // S[2] matches the RTL XOR with the carry generated from bits 0 and 1.
    check_sum_bit2: assert property (
        @($global_clock) S[2] == (A[2] ^ B[2] ^
            ((A[1] & B[1]) | (A[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0))) |
             (B[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0)))))
    );

    // S[3] matches the RTL XOR with the carry generated from bits 0 through 2.
    check_sum_bit3: assert property (
        @($global_clock) S[3] == (A[3] ^ B[3] ^
            ((A[2] & B[2]) |
             (A[2] & ((A[1] & B[1]) | (A[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0))) |
                      (B[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0))))) |
             (B[2] & ((A[1] & B[1]) | (A[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0))) |
                      (B[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0)))))))
    );

    // C_out matches the RTL carry generated from bits 0 through 3.
    check_carry_out: assert property (
        @($global_clock) C_out == ((A[3] & B[3]) |
            (A[3] & ((A[2] & B[2]) |
                     (A[2] & ((A[1] & B[1]) | (A[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0))) |
                              (B[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0))))) |
                     (B[2] & ((A[1] & B[1]) | (A[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0))) |
                              (B[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0))))))) |
            (B[3] & ((A[2] & B[2]) |
                     (A[2] & ((A[1] & B[1]) | (A[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0))) |
                              (B[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0))))) |
                     (B[2] & ((A[1] & B[1]) | (A[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0))) |
                              (B[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0))))))))
    );

endmodule