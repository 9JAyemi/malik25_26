
module four_bit_adder (
    input [3:0] A,
    input [3:0] B,
    input C_in,
    output [3:0] S,
    output C_out
);

    wire [3:0] c1, c2, c3;

    // First column
    assign c1[0] = A[0] & B[0];
    assign S[0] = A[0] ^ B[0] ^ C_in;

    // Second column
    assign c1[1] = A[1] ^ B[1];
    assign c2[1] = c1[0] & c1[1];
    assign S[1] = A[1] ^ B[1] ^ C_in;
    assign C_out = c1[0] & c1[1] | A[1] & B[1];

    // Third column
    assign c1[2] = A[2] ^ B[2];
    assign c2[2] = c1[1] & c1[2];
    assign c3[2] = c2[1] ^ c2[2];
    assign S[2] = A[2] ^ B[2] ^ C_in;

    // Fourth column
    assign c1[3] = A[3] ^ B[3];
    assign c2[3] = c1[2] & c1[3];
    assign c3[3] = c2[2] ^ c2[3];
    assign S[3] = A[3] ^ B[3] ^ C_in;

endmodule