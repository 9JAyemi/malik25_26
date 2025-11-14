module ripple_carry_adder (
  input [3:0] A,
  input [3:0] B,
  input Cin,
  output [3:0] S,
  output Cout
);

  wire [3:0] carry;
  
  full_adder fa0(A[0], B[0], Cin, S[0], carry[0]);
  full_adder fa1(A[1], B[1], carry[0], S[1], carry[1]);
  full_adder fa2(A[2], B[2], carry[1], S[2], carry[2]);
  full_adder fa3(A[3], B[3], carry[2], S[3], Cout);

endmodule
module full_adder (
  input A,
  input B,
  input Cin,
  output S,
  output Cout
);

  assign S = A ^ B ^ Cin;
  assign Cout = (A & B) | (Cin & (A ^ B));

endmodule
