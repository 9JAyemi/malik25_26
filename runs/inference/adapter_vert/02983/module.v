
module adder(
    input [3:0] A,
    input [3:0] B,
    output [3:0] S,
    output C_out
);

    wire [3:0] c;

    assign S[0] = A[0] ^ B[0] ^ 1'b0;
    assign c[0] = (A[0] & B[0]) | (A[0] & 1'b0) | (B[0] & 1'b0);

    assign S[1] = A[1] ^ B[1] ^ c[0];
    assign c[1] = (A[1] & B[1]) | (A[1] & c[0]) | (B[1] & c[0]);

    assign S[2] = A[2] ^ B[2] ^ c[1];
    assign c[2] = (A[2] & B[2]) | (A[2] & c[1]) | (B[2] & c[1]);

    assign S[3] = A[3] ^ B[3] ^ c[2];
    assign C_out = (A[3] & B[3]) | (A[3] & c[2]) | (B[3] & c[2]);

endmodule
