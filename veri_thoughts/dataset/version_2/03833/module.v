
module four_bit_adder(
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output [3:0] Z,
    output Cout
);

    wire [3:0] sum;
    wire [3:0] c;

    assign sum[0] = A[0] ^ B[0] ^ Cin;
    assign c[0] = (A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin);

    assign sum[1] = A[1] ^ B[1] ^ c[0];
    assign c[1] = (A[1] & B[1]) | (A[1] & c[0]) | (B[1] & c[0]);

    assign sum[2] = A[2] ^ B[2] ^ c[1];
    assign c[2] = (A[2] & B[2]) | (A[2] & c[1]) | (B[2] & c[1]);

    assign sum[3] = A[3] ^ B[3] ^ c[2];
    assign c[3] = (A[3] & B[3]) | (A[3] & c[2]) | (B[3] & c[2]);

    assign Cout = c[3];
    assign Z = sum;

endmodule