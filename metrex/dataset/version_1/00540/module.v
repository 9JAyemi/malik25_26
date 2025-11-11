module adder4 (
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output [3:0] S,
    output Cout
);

    wire [3:0] c, s;

    // Full adder implementation
    assign c[0] = A[0] & B[0];
    assign s[0] = A[0] ^ B[0] ^ Cin;
    assign c[1] = (A[0] & B[0]) | (A[1] & B[0]) | (A[0] & B[1]);
    assign s[1] = A[1] ^ B[1] ^ c[0];
    assign c[2] = (A[0] & B[1]) | (A[1] & B[0]) | (A[2] & B[0]) | (A[1] & B[1]) | (A[0] & B[2]);
    assign s[2] = A[2] ^ B[2] ^ c[1];
    assign c[3] = (A[0] & B[2]) | (A[1] & B[1]) | (A[2] & B[0]) | (A[3] & B[0]) | (A[2] & B[1]) | (A[1] & B[2]) | (A[0] & B[3]);
    assign s[3] = A[3] ^ B[3] ^ c[2];

    // Assign outputs
    assign S = s;
    assign Cout = c[3];

endmodule