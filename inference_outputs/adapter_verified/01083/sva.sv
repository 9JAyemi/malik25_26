module adder_sva (
    input logic clk,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [8:0] sum
);

// Sum must equal the 8-bit addition of A and B.
    check_sum_matches_addition: assert property (
        @(posedge clk) sum == ({1'b0, A} + {1'b0, B})
    );

// LSB of sum must equal the XOR of A[0] and B[0].
    check_lsb_xor: assert property (
        @(posedge clk) sum[0] == (A[0] ^ B[0])
    );

// Bit 1 of sum must equal the XOR of A[1] and B[1] with the carry from bit 0.
    check_bit1_xor_with_c0: assert property (
        @(posedge clk) sum[1] == (A[1] ^ B[1] ^ (({1'b0, A} + {1'b0, B})[0]))
    );

// Bit 2 of sum must equal the XOR of A[2] and B[2] with the carry from bit 1.
    check_bit2_xor_with_c1: assert property (
        @(posedge clk) sum[2] == (A[2] ^ B[2] ^ (({1'b0, A} + {1'b0, B})[1]))
    );

// Bit 3 of sum must equal the XOR of A[3] and B[3] with the carry from bit 2.
    check_bit3_xor_with_c2: assert property (
        @(posedge clk) sum[3] == (A[3] ^ B[3] ^ (({1'b0, A} + {1'b0, B})[2]))
    );

// Bit 4 of sum must equal the XOR of A[4] and B[4] with the carry from bit 3.
    check_bit4_xor_with_c3: assert property (
        @(posedge clk) sum[4] == (A[4] ^ B[4] ^ (({1'b0, A} + {1'b0, B})[3]))
    );

// Bit 5 of sum must equal the XOR of A[5] and B[5] with the carry from bit 4.
    check_bit5_xor_with_c4: assert property (
        @(posedge clk) sum[5] == (A[5] ^ B[5] ^ (({1'b0, A} + {1'b0, B})[4]))
    );

// Bit 6 of sum must equal the XOR of A[6] and B[6] with the carry from bit 5.
    check_bit6_xor_with_c5: assert property (
        @(posedge clk) sum[6] == (A[6] ^ B[6] ^ (({1'b0, A} + {1'b0, B})[5]))
    );

// Bit 7 of sum must equal the XOR of A[7] and B[7] with the carry from bit 6.
    check_bit7_xor_with_c6: assert property (
        @(posedge clk) sum[7] == (A[7] ^ B[7] ^ (({1'b0, A} + {1'b0, B})[6]))
    );

// Bit 8 of sum must equal the carry out from the 7-bit addition.
    check_msb_carry_out: assert property (
        @(posedge clk) sum[8] == (({1'b0, A} + {1'b0, B})[7])
    );

endmodule
