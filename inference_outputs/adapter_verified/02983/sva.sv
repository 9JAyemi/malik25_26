module adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S,
    input logic C_out
);

// Sum bit 0 matches the RTL equation.
    check_sum_bit0: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0] ^ 1'b0)
    );

// Sum bit 1 uses the carry generated from bit 0.
    check_sum_bit1: assert property (
        @(posedge clk) S[1] == (A[1] ^ B[1] ^ ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0)))
    );

// Sum bit 2 uses the carry generated from bit 1.
    check_sum_bit2: assert property (
        @(posedge clk) S[2] == (A[2] ^ B[2] ^ ((A[1] & B[1]) | (A[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0))) | (B[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0)))))
    );

// Sum bit 3 uses the carry generated from bit 2.
    check_sum_bit3: assert property (
        @(posedge clk) S[3] == (A[3] ^ B[3] ^ ((A[2] & B[2]) | (A[2] & ((A[1] & B[1]) | (A[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0))) | (B[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0))))) | (B[2] & ((A[1] & B[1]) | (A[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0))) | (B[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0)))))))
    );

// C_out matches the RTL carry-out equation.
    check_cout_equation: assert property (
        @(posedge clk) C_out == ((A[3] & B[3]) | (A[3] & ((A[2] & B[2]) | (A[2] & ((A[1] & B[1]) | (A[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0))) | (B[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0))))) | (B[2] & ((A[1] & B[1]) | (A[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0))) | (B[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0)))))))
    );

// The 4-bit output matches the RTL full-adder chain.
    check_full_adder_result: assert property (
        @(posedge clk) {C_out, S} == ({1'b0, A} + {1'b0, B})
    );

endmodule
