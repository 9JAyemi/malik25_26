module four_bit_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S,
    input logic COUT
);

// Bit 0 sum matches the first full-adder XOR equation.
    check_bit0_sum: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0] ^ 1'b0)
    );

// Bit 1 sum uses the carry generated from bit 0.
    check_bit1_sum: assert property (
        @(posedge clk) S[1] == (A[1] ^ B[1] ^ ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0)))
    );

// Bit 2 sum uses the carry generated from bit 1.
    check_bit2_sum: assert property (
        @(posedge clk) S[2] == (A[2] ^ B[2] ^ ((A[1] & B[1]) | (A[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0))) | (B[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0)))))
    );

// Bit 3 sum uses the carry generated from bit 2.
    check_bit3_sum: assert property (
        @(posedge clk) S[3] == (A[3] ^ B[3] ^ ((A[2] & B[2]) | (A[2] & ((A[1] & B[1]) | (A[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0))) | (B[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0))))) | (B[2] & ((A[1] & B[1]) | (A[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0))) | (B[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0)))))))
    );

// COUT matches the carry generated from bit 3.
    check_cout: assert property (
        @(posedge clk) COUT == ((A[3] & B[3]) | (A[3] & ((A[2] & B[2]) | (A[2] & ((A[1] & B[1]) | (A[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0))) | (B[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0))))) | (B[2] & ((A[1] & B[1]) | (A[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0))) | (B[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0))))))) | (B[3] & ((A[2] & B[2]) | (A[2] & ((A[1] & B[1]) | (A[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0))) | (B[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0))))) | (B[2] & ((A[1] & B[1]) | (A[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0))) | (B[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0))))))))
    );

endmodule
