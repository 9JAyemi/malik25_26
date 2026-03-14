module adder_4bit_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S,
    input logic C_out
);
    // 5-bit sum must equal unsigned addition of A and B.
    check_sum_5bit: assert property (
        @(posedge CLK) disable iff (1'b0) {C_out, S} == ({1'b0, A} + {1'b0, B})
    );

    // LSB sum equals A[0] XOR B[0] (carry-in is 0).
    check_s0_xor: assert property (
        @(posedge CLK) disable iff (1'b0) S[0] == (A[0] ^ B[0])
    );

    // Bit1 sum equals A[1] XOR B[1] XOR carry0.
    check_s1_ripple: assert property (
        @(posedge CLK) disable iff (1'b0) S[1] == (A[1] ^ B[1] ^ (A[0] & B[0]))
    );

    // Bit2 sum equals A[2] XOR B[2] XOR carry1.
    check_s2_ripple: assert property (
        @(posedge CLK) disable iff (1'b0) S[2] == (A[2] ^ B[2] ^ ((A[1] & B[1]) | ((A[1] ^ B[1]) & (A[0] & B[0]))))
    );

    // Bit3 sum equals A[3] XOR B[3] XOR carry2.
    check_s3_ripple: assert property (
        @(posedge CLK) disable iff (1'b0) S[3] == (A[3] ^ B[3] ^ ((A[2] & B[2]) | ((A[2] ^ B[2]) & ((A[1] & B[1]) | ((A[1] ^ B[1]) & (A[0] & B[0]))))))
    );

    // Final carry-out equals majority of A[3], B[3], and carry2.
    check_cout_ripple: assert property (
        @(posedge CLK) disable iff (1'b0)
            C_out == (
                (A[3] & B[3]) |
                (A[3] & ((A[2] & B[2]) | ((A[2] ^ B[2]) & ((A[1] & B[1]) | ((A[1] ^ B[1]) & (A[0] & B[0])))))) |
                (B[3] & ((A[2] & B[2]) | ((A[2] ^ B[2]) & ((A[1] & B[1]) | ((A[1] ^ B[1]) & (A[0] & B[0]))))))
            )
    );

    // Output S equals lower 4 bits of the 5-bit sum.
    check_s_lowbits_of_sum: assert property (
        @(posedge CLK) disable iff (1'b0) S == (({1'b0, A} + {1'b0, B})[3:0])
    );

    // Carry-out equals MSB of the 5-bit sum.
    check_cout_msb_of_sum: assert property (
        @(posedge CLK) disable iff (1'b0) C_out == (({1'b0, A} + {1'b0, B})[4])
    );

    // Adding zero on A yields S==B and no carry.
    check_add_zero_A: assert property (
        @(posedge CLK) disable iff (1'b0) (A == 4'b0000) |-> (S == B) && (C_out == 1'b0)
    );

    // Adding zero on B yields S==A and no carry.
    check_add_zero_B: assert property (
        @(posedge CLK) disable iff (1'b0) (B == 4'b0000) |-> (S == A) && (C_out == 1'b0)
    );

    // When both inputs are 4'hF, sum is 4'he with carry-out 1.
    check_max_plus_max: assert property (
        @(posedge CLK) disable iff (1'b0) (A == 4'hF && B == 4'hF) |-> (S == 4'hE) && (C_out == 1'b1)
    );

    // Carry-out iff the 4-bit sum wraps below either operand.
    check_cout_wrap_condition: assert property (
        @(posedge CLK) disable iff (1'b0) C_out == ((S < A) || (S < B))
    );
endmodule