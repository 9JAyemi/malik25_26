module four_bit_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] sum
);

// Sum equals A + B (4-bit wraparound).
    check_sum_matches_addition: assert property (
        @(posedge clk) sum == (A + B)
    );

// Bit 0 sum matches the first full adder.
    check_lsb_sum: assert property (
        @(posedge clk) sum[0] == (A[0] ^ B[0] ^ 1'b0)
    );

// Bit 1 sum uses the carry from bit 0.
    check_bit1_sum: assert property (
        @(posedge clk) sum[1] == (A[1] ^ B[1] ^ ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0)))
    );

// Bit 2 sum uses the carry from bit 1.
    check_bit2_sum: assert property (
        @(posedge clk) sum[2] == (A[2] ^ B[2] ^ ((A[1] & B[1]) | (A[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0))) | (B[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0)))))
    );

// Bit 3 sum uses the carry from bit 2.
    check_msb_sum: assert property (
        @(posedge clk) sum[3] == (A[3] ^ B[3] ^ ((A[2] & B[2]) | (A[2] & ((A[1] & B[1]) | (A[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0))) | (B[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0))))) | (B[2] & ((A[1] & B[1]) | (A[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0))) | (B[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0)))))))
    );

endmodule
