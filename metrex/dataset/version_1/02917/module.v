
module ripple_carry_adder(
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output [3:0] S,
    output Cout
);

    assign S[0] = A[0] ^ B[0] ^ Cin;
    assign S[1] = A[1] ^ B[1] ^ (S[0] & 1'b1);
    assign S[2] = A[2] ^ B[2] ^ (S[1] & 1'b1);
    assign S[3] = A[3] ^ B[3] ^ (S[2] & 1'b1);
    assign Cout = (A[3] & B[3]) | ((A[3] | B[3]) & Cin);

endmodule
