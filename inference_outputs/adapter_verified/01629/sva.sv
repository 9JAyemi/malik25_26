module binary_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] C
);

// C[0] matches the RTL sum bit equation.
    check_sum_bit0: assert property (
        @(posedge clk) C[0] == (A[0] ^ B[0] ^ 1'b0)
    );

// C[1] matches the RTL sum bit equation.
    check_sum_bit1: assert property (
        @(posedge clk) C[1] == (A[1] ^ B[1] ^ ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0)))
    );

// C[2] matches the RTL sum bit equation.
    check_sum_bit2: assert property (
        @(posedge clk) C[2] == (A[2] ^ B[2] ^ ((A[1] & B[1]) | (A[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0))) | (B[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0)))))
    );

// C[3] matches the RTL sum bit equation.
    check_sum_bit3: assert property (
        @(posedge clk) C[3] == (A[3] ^ B[3] ^ ((A[2] & B[2]) | (A[2] & ((A[1] & B[1]) | (A[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0))) | (B[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0))))) | (B[2] & ((A[1] & B[1]) | (A[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0))) | (B[1] & ((A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0)))))))
    );

endmodule
