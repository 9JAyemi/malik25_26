module four_bit_adder_sva (
    input logic        clk,
    input logic [3:0]  A,
    input logic [3:0]  B,
    input logic        Ci,
    input logic [3:0]  S,
    input logic        Co
);

// The 4-bit output matches A + B + Ci.
    check_total_sum: assert property (
        @(posedge clk) disable iff (1'b0)
        {Co, S} == ({1'b0, A} + {1'b0, B} + Ci)
    );

// Bit 0 sum is the XOR of A[0], B[0], and Ci.
    check_bit0_sum: assert property (
        @(posedge clk) disable iff (1'b0)
        S[0] == (A[0] ^ B[0] ^ Ci)
    );

// Bit 1 sum uses the carry generated from bit 0.
    check_bit1_sum: assert property (
        @(posedge clk) disable iff (1'b0)
        S[1] == (A[1] ^ B[1] ^ ((A[0] & B[0]) | ((A[0] ^ B[0]) & Ci)))
    );

// Bit 2 sum uses the carry generated from bit 1.
    check_bit2_sum: assert property (
        @(posedge clk) disable iff (1'b0)
        S[2] == (A[2] ^ B[2] ^ ((A[1] & B[1]) | ((A[1] ^ B[1]) & ((A[0] & B[0]) | ((A[0] ^ B[0]) & Ci)))))
    );

// Bit 3 sum uses the carry generated from bit 2.
    check_bit3_sum: assert property (
        @(posedge clk) disable iff (1'b0)
        S[3] == (A[3] ^ B[3] ^ ((A[2] & B[2]) | ((A[2] ^ B[2]) & ((A[1] & B[1]) | ((A[1] ^ B[1]) & ((A[0] & B[0]) | ((A[0] ^ B[0]) & Ci)))))))
    );

// Carry out is the final carry generated from bit 3.
    check_carry_out: assert property (
        @(posedge clk) disable iff (1'b0)
        Co == ((A[3] & B[3]) | ((A[3] ^ B[3]) & ((A[2] & B[2]) | ((A[2] ^ B[2]) & ((A[1] & B[1]) | ((A[1] ^ B[1]) & ((A[0] & B[0]) | ((A[0] ^ B[0]) & Ci))))))))
    );

endmodule
