module FOURBITADDER
(
  input [3:0] A,
  input [3:0] B,
  input Cin,
  output [3:0] S,
  output Cout
);

  wire [3:0] c;

  FULLADDER fa0(A[0], B[0], Cin, c[0], S[0]);
  FULLADDER fa1(A[1], B[1], c[0], c[1], S[1]);
  FULLADDER fa2(A[2], B[2], c[1], c[2], S[2]);
  FULLADDER fa3(A[3], B[3], c[2], Cout, S[3]);

endmodule

module FULLADDER
(
  input A,
  input B,
  input Cin,
  output Cout,
  output S
);

  assign S = A^B^Cin;
  assign Cout = (A&B)|(B&Cin)|(A&Cin);

endmodule