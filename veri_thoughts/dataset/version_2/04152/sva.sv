module adder_4bit_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Ci,
    input logic [3:0] S,
    input logic Co
);

    function automatic logic carry3(input logic a, input logic b, input logic c);
        carry3 = (a & b) | ((a ^ b) & c);
    endfunction

    // Outputs must match 4-bit addition with carry-in.
    check_full_sum: assert property (
        @($global_clock) {Co, S} == ({1'b0, A} + {1'b0, B} + {4'b0, Ci})
    );

    // Sum bit 0 is the XOR of A[0], B[0], and Ci.
    check_sum_bit0: assert property (
        @($global_clock) S[0] == (A[0] ^ B[0] ^ Ci)
    );

    // Sum bit 1 uses the carry from bit 0.
    check_sum_bit1: assert property (
        @($global_clock) S[1] == (A[1] ^ B[1] ^ carry3(A[0], B[0], Ci))
    );

    // Sum bit 2 uses the carry from bit 1.
    check_sum_bit2: assert property (
        @($global_clock) S[2] == (A[2] ^ B[2] ^ carry3(A[1], B[1], carry3(A[0], B[0], Ci)))
    );

    // Sum bit 3 uses the carry from bit 2.
    check_sum_bit3: assert property (
        @($global_clock) S[3] == (A[3] ^ B[3] ^ carry3(A[2], B[2], carry3(A[1], B[1], carry3(A[0], B[0], Ci))))
    );

    // Carry-out is the carry from the most significant stage.
    check_carry_out: assert property (
        @($global_clock) Co == carry3(A[3], B[3], carry3(A[2], B[2], carry3(A[1], B[1], carry3(A[0], B[0], Ci))))
    );

    // Zero operands leave only the carry-in in the result.
    check_zero_operands: assert property (
        @($global_clock) (A == 4'b0000 && B == 4'b0000) |-> (S == {3'b000, Ci} && Co == 1'b0)
    );

    // With B and Ci low, the adder passes A through unchanged.
    check_pass_through_a: assert property (
        @($global_clock) (B == 4'b0000 && Ci == 1'b0) |-> (S == A && Co == 1'b0)
    );

    // With A and Ci low, the adder passes B through unchanged.
    check_pass_through_b: assert property (
        @($global_clock) (A == 4'b0000 && Ci == 1'b0) |-> (S == B && Co == 1'b0)
    );

    // With B low and Ci high, the adder increments A by one.
    check_increment_a: assert property (
        @($global_clock) (B == 4'b0000 && Ci == 1'b1) |-> ({Co, S} == ({1'b0, A} + 5'b00001))
    );

endmodule