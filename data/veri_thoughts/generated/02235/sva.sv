module my_4_bit_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S
);
    ///// Functional correctness of 4-bit ripple adder (Cin=0) /////
    // Sum matches 4-bit addition A+B modulo 16.
    check_sum_mod16: assert property (
        @(posedge clk) S == (A + B)
    );

    // LSB is XOR of LSBs (no carry-in).
    check_lsb_xor: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0])
    );

    // Bit[1] sum equals A1^B1 with carry from bit[0] = A0&B0.
    check_bit1_sum: assert property (
        @(posedge clk) S[1] == ((A[1] ^ B[1]) ^ (A[0] & B[0]))
    );

    // Bit[2] sum equals A2^B2 with carry c1 = g1 | (p1 & c0).
    check_bit2_sum: assert property (
        @(posedge clk) S[2] == ((A[2] ^ B[2]) ^ ((A[1] & B[1]) | ((A[1] ^ B[1]) & (A[0] & B[0]))))
    );

    // Bit[3] sum equals A3^B3 with carry c2 = g2 | (p2 & c1).
    check_bit3_sum: assert property (
        @(posedge clk) S[3] == ((A[3] ^ B[3]) ^ ((A[2] & B[2]) | ((A[2] ^ B[2]) & ((A[1] & B[1]) | ((A[1] ^ B[1]) & (A[0] & B[0]))))))
    );

    ///// Useful arithmetic identities that must hold /////
    // Adding zero leaves the other operand unchanged (A==0).
    check_identity_A_zero: assert property (
        @(posedge clk) (A == 4'b0000) |-> (S == B)
    );

    // Adding zero leaves the other operand unchanged (B==0).
    check_identity_B_zero: assert property (
        @(posedge clk) (B == 4'b0000) |-> (S == A)
    );

    // When A==B, sum equals A<<1 modulo 16.
    check_double_when_equal: assert property (
        @(posedge clk) (A == B) |-> (S == {A[2:0], 1'b0})
    );

    // Complementary operands sum to all ones (modulo 16).
    check_complement_all_ones: assert property (
        @(posedge clk) (A == ~B) |-> (S == 4'hF)
    );

    // Adding 0xF decrements the other operand modulo 16.
    check_minus_one_when_A_all_ones: assert property (
        @(posedge clk) (A == 4'hF) |-> (S == (B - 4'd1))
    );
endmodule