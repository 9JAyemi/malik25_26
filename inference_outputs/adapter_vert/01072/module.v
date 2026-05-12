module full_adder(
    input A,
    input B,
    input Cin,
    output S,
    output Cout
);

assign S = A ^ B ^ Cin;
assign Cout = (A & B) | (B & Cin) | (A & Cin);

endmodule

module four_bit_adder(
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output [3:0] S,
    output C_out
);

  wire c0, c1, c2;
  full_adder fa0(A[0], B[0], Cin, S[0], c0);
  full_adder fa1(A[1], B[1], c0, S[1], c1);
  full_adder fa2(A[2], B[2], c1, S[2], c2);
  full_adder fa3(A[3], B[3], c2, S[3], C_out);

endmodule