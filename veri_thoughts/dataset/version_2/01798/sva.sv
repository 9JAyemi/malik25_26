module adder4bit_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic C_in,
    input logic [3:0] S,
    input logic C_out
);
    // Sum+carry concatenation equals zero-extended 4-bit addition result.
    check_concat_sum: assert property (
        @(posedge CLK) {C_out, S} == {1'b0, (A + B + C_in)}
    );

    // Sum equals 4-bit truncated A+B+C_in.
    check_sum_lower4: assert property (
        @(posedge CLK) S == (A + B + C_in)
    );

    // Carry-out is always zero due to 4-bit addition width.
    check_cout_zero: assert property (
        @(posedge CLK) C_out == 1'b0
    );

    // Bit0 of sum is XOR of A0, B0, and C_in.
    check_bit0_xor: assert property (
        @(posedge CLK) S[0] == (A[0] ^ B[0] ^ C_in)
    );

    // Bit1 of sum uses carry from bit0.
    check_bit1_xor_with_c0: assert property (
        @(posedge CLK) S[1] == (A[1] ^ B[1] ^ ((A[0]&B[0]) | (A[0]&C_in) | (B[0]&C_in)))
    );

    // Bit2 of sum uses carry from bit1 (which depends on bit0).
    check_bit2_xor_with_c1: assert property (
        @(posedge CLK) S[2] == (
            A[2] ^ B[2] ^
            ( (A[1]&B[1]) |
              (A[1]&((A[0]&B[0]) | (A[0]&C_in) | (B[0]&C_in))) |
              (B[1]&((A[0]&B[0]) | (A[0]&C_in) | (B[0]&C_in))) )
        )
    );

    // Bit3 of sum uses carry from bit2 (which depends on bits1..0).
    check_bit3_xor_with_c2: assert property (
        @(posedge CLK) S[3] == (
            A[3] ^ B[3] ^
            ( (A[2]&B[2]) |
              (A[2] &
                 ( (A[1]&B[1]) |
                   (A[1]&((A[0]&B[0]) | (A[0]&C_in) | (B[0]&C_in))) |
                   (B[1]&((A[0]&B[0]) | (A[0]&C_in) | (B[0]&C_in))) )
              ) |
              (B[2] &
                 ( (A[1]&B[1]) |
                   (A[1]&((A[0]&B[0]) | (A[0]&C_in) | (B[0]&C_in))) |
                   (B[1]&((A[0]&B[0]) | (A[0]&C_in) | (B[0]&C_in))) )
              )
            )
        )
    );

    // Adding zero operand and zero carry returns the other operand (B zero).
    check_add_zero_identity_Bzero: assert property (
        @(posedge CLK) (B == 4'b0000 && C_in == 1'b0) |-> (S == A && C_out == 1'b0)
    );

    // Adding zero operand and zero carry returns the other operand (A zero).
    check_add_zero_identity_Azero: assert property (
        @(posedge CLK) (A == 4'b0000 && C_in == 1'b0) |-> (S == B && C_out == 1'b0)
    );

    // All zeros in yields all zeros out.
    check_all_zero_pass_through: assert property (
        @(posedge CLK) (A == 4'b0000 && B == 4'b0000 && C_in == 1'b0) |-> (S == 4'b0000 && C_out == 1'b0)
    );
endmodule