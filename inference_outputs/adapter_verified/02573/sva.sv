module ripple_carry_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] OUT
);

// OUT equals 4-bit sum of A and B.
    check_total_sum: assert property (
        @(posedge clk) OUT == (A + B)
    );

// LSB sum is XOR of A[0] and B[0].
    check_lsb_sum: assert property (
        @(posedge clk) OUT[0] == (A[0] ^ B[0])
    );

// Bit1 sum uses carry generated from bit0.
    check_bit1_sum: assert property (
        @(posedge clk) OUT[1] == (A[1] ^ B[1] ^ ((A[0] & B[0]) | (A[0] & ~B[0]) & (~A[1] & B[1])))
    );

// Bit2 sum uses carry generated from bits0:1.
    check_bit2_sum: assert property (
        @(posedge clk) OUT[2] == (A[2] ^ B[2] ^ ((A[1] & B[1]) | (A[1] & ~B[1]) & (~A[2] & B[2])))
    );

// Bit3 sum uses carry generated from bits0:2.
    check_bit3_sum: assert property (
        @(posedge clk) OUT[3] == (A[3] ^ B[3] ^ ((A[2] & B[2]) | (A[2] & ~B[2]) & (~A[3] & B[3])))
    );

endmodule
