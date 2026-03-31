```systemverilog
module adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S,
    input logic C_out
);

    // Combinational logic: S and C_out are determined by A and B
    // S[0] = A[0] ^ B[0] ^ 1'b0
    // S[1] = A[1] ^ B[1] ^ c[0]
    // S[2] = A[2] ^ B[2] ^ c[1]
    // S[3] = A[3] ^ B[3] ^ c[2]
    // C_out = (A[3] & B[3]) | (A[3] & c[2]) | (B[3] & c[2])

    // S[0] is calculated correctly
    check_S0: assert property (
        @(posedge CLK) disable iff (!RESETn) S[0] == (A[0] ^ B[0] ^ 1'b0)
    );

    // S[1] is calculated correctly
    check_S1: assert property (
        @(posedge CLK) disable iff (!RESETn) S[1] == (A[1] ^ B[1] ^ (A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0))
    );

    // S[2] is calculated correctly
    check_S2: assert property (
        @(posedge CLK) disable iff (!RESETn) S[2] == (A[2] ^ B[2] ^ ((A[1] & B[1]) | (A[1] & (A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0)) | (B[1] & (A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0))))
    );

    // S[3] is calculated correctly
    check_S3: assert property (
        @(posedge CLK) disable iff (!RESETn) S[3] == (A[3] ^ B[3] ^ (((A[2] & B[2]) | (A[2] & ((A[1] & B[1]) | (A[1] & (A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0)) | (B[1] & (A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0)))) | (B[2] & ((A[1] & B[1]) | (A[1] & (A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0)) | (B[1] & (A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0)))))))
    );

    // C_out is calculated correctly
    check_C_out: assert property (
        @(posedge CLK) disable iff (!RESETn) C_out == ((A[3] & B[3]) | (A[3] & (((A[2] & B[2]) | (A[2] & ((A[1] & B[1]) | (A[1] & (A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0)) | (B[1] & (A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0)))) | (B[2] & ((A[1] & B[1]) | (A[1] & (A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0)) | (B[1] & (A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0)))))))
    );

endmodule
```