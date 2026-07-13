module adder_4bit_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       reset,
    input logic [3:0] S
);

    // The output matches 4-bit addition of A, B, and the bit-0 carry-in.
    check_sum_matches_addition: assert property (
        @($global_clock) S == (A + B + reset)
    );

    // Sum bit 0 is the XOR of A[0], B[0], and reset.
    check_bit0_sum: assert property (
        @($global_clock) S[0] == (A[0] ^ B[0] ^ reset)
    );

    // Sum bit 1 uses the carry generated from bit 0.
    check_bit1_sum: assert property (
        @($global_clock)
        S[1] == (A[1] ^ B[1] ^
                 ((A[0] & B[0]) | (A[0] & reset) | (B[0] & reset)))
    );

    // Sum bit 2 uses the carry generated from bits 0 and 1.
    check_bit2_sum: assert property (
        @($global_clock)
        S[2] == (A[2] ^ B[2] ^
                 ((A[1] & B[1]) |
                  (A[1] & ((A[0] & B[0]) | (A[0] & reset) | (B[0] & reset))) |
                  (B[1] & ((A[0] & B[0]) | (A[0] & reset) | (B[0] & reset)))))
    );

    // Sum bit 3 uses the carry generated from bits 0 through 2.
    check_bit3_sum: assert property (
        @($global_clock)
        S[3] == (A[3] ^ B[3] ^
                 ((A[2] & B[2]) |
                  (A[2] & ((A[1] & B[1]) |
                           (A[1] & ((A[0] & B[0]) | (A[0] & reset) | (B[0] & reset))) |
                           (B[1] & ((A[0] & B[0]) | (A[0] & reset) | (B[0] & reset))))) |
                  (B[2] & ((A[1] & B[1]) |
                           (A[1] & ((A[0] & B[0]) | (A[0] & reset) | (B[0] & reset))) |
                           (B[1] & ((A[0] & B[0]) | (A[0] & reset) | (B[0] & reset)))))))
    );

    // With no carry-in and B at zero, S passes A through.
    check_a_passthrough_when_b_zero: assert property (
        @($global_clock) ((B == 4'h0) && (reset == 1'b0)) |-> (S == A)
    );

    // With no carry-in and A at zero, S passes B through.
    check_b_passthrough_when_a_zero: assert property (
        @($global_clock) ((A == 4'h0) && (reset == 1'b0)) |-> (S == B)
    );

    // With both operands at zero, only the input carry appears on bit 0.
    check_zero_operands_follow_input_carry: assert property (
        @($global_clock) ((A == 4'h0) && (B == 4'h0)) |-> (S == {3'b000, reset})
    );

endmodule