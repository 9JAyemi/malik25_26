module four_bit_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S,
    input logic C
);
    // Local recompute of ripple-carry chain from A and B
    logic c1, c2, c3;
    logic [4:0] exp_sum5;

    assign c1 = A[0] & B[0];
    assign c2 = (A[1] & B[1]) | (A[1] & c1) | (B[1] & c1);
    assign c3 = (A[2] & B[2]) | (A[2] & c2) | (B[2] & c2);
    assign exp_sum5 = {1'b0, A} + {1'b0, B};

    // The 5-bit result {C,S} equals A+B with zero carry-in.
    check_vector_sum_matches_add: assert property (
        @(posedge clk) disable iff (1'b0) ({C, S} == exp_sum5)
    );

    // LSB sum is XOR of A[0] and B[0] (c_in=0).
    check_sum_bit0_xor: assert property (
        @(posedge clk) disable iff (1'b0) (S[0] == (A[0] ^ B[0]))
    );

    // Bit1 sum equals XOR of A[1], B[1], and c1.
    check_sum_bit1_xor_with_c1: assert property (
        @(posedge clk) disable iff (1'b0) (S[1] == (A[1] ^ B[1] ^ c1))
    );

    // Bit2 sum equals XOR of A[2], B[2], and c2.
    check_sum_bit2_xor_with_c2: assert property (
        @(posedge clk) disable iff (1'b0) (S[2] == (A[2] ^ B[2] ^ c2))
    );

    // Bit3 sum equals XOR of A[3], B[3], and c3.
    check_sum_bit3_xor_with_c3: assert property (
        @(posedge clk) disable iff (1'b0) (S[3] == (A[3] ^ B[3] ^ c3))
    );

    // Final carry-out equals majority of A[3], B[3], and c3.
    check_carryout_majority: assert property (
        @(posedge clk) disable iff (1'b0) (C == ((A[3] & B[3]) | (A[3] & c3) | (B[3] & c3)))
    );

    // Carry-out equals MSB of the 5-bit sum.
    check_carryout_equals_sum_msb: assert property (
        @(posedge clk) disable iff (1'b0) (C == exp_sum5[4])
    );

    // Sum lower 4 bits equal lower 4 bits of A+B.
    check_sum_lower4_equals_add: assert property (
        @(posedge clk) disable iff (1'b0) (S == exp_sum5[3:0])
    );

    // Adding zero on A yields S=B and C=0.
    check_add_zero_on_A: assert property (
        @(posedge clk) disable iff (1'b0) ((A == 4'b0000) |-> (S == B) && (C == 1'b0))
    );

    // Adding zero on B yields S=A and C=0.
    check_add_zero_on_B: assert property (
        @(posedge clk) disable iff (1'b0) ((B == 4'b0000) |-> (S == A) && (C == 1'b0))
    );

    // If no bit position has both A and B set, result is XOR and no carry.
    check_no_overlap_bits_implies_xor: assert property (
        @(posedge clk) disable iff (1'b0) (((A & B) == 4'b0000) |-> (S == (A ^ B)) && (C == 1'b0))
    );

endmodule