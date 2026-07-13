module adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] C
);

// C must equal the 4-bit sum of A and B.
    check_sum_matches_addition: assert property (
        @(posedge clk) C == (A + B)
    );

// Bit 0 of C must match the least-significant sum bit.
    check_lsb_sum: assert property (
        @(posedge clk) C[0] == (A[0] ^ B[0])
    );

// Bit 1 of C must include the carry from bit 0.
    check_bit1_sum: assert property (
        @(posedge clk) C[1] == (A[1] ^ B[1] ^ (A[0] & B[0]))
    );

// Bit 2 of C must include the carry from bits 0 and 1.
    check_bit2_sum: assert property (
        @(posedge clk) C[2] == (A[2] ^ B[2] ^ ((A[1] & B[1]) | ((A[0] & B[0]) & (A[1] | B[1]))))
    );

// Bit 3 of C must include the carry from bits 0 through 2.
    check_bit3_sum: assert property (
        @(posedge clk) C[3] == (A[3] ^ B[3] ^ ((A[2] & B[2]) | ((A[1] & B[1]) & (A[2] | B[2])) | ((A[0] & B[0]) & (A[1] | B[1]) & (A[2] | B[2]))))
    );

endmodule
