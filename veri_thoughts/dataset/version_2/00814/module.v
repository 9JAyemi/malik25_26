module ripple_carry_adder(
  input [3:0] A,
  input [3:0] B,
  input Cin,
  output [3:0] Sum,
  output Cout
);

  wire [3:0] carry;
  
  // full adder for bit 0
  full_adder fa0(A[0], B[0], Cin, Sum[0], carry[0]);
  
  // full adders for bits 1-3
  full_adder fa1(A[1], B[1], carry[0], Sum[1], carry[1]);
  full_adder fa2(A[2], B[2], carry[1], Sum[2], carry[2]);
  full_adder fa3(A[3], B[3], carry[2], Sum[3], Cout);
  
endmodule

module full_adder(
  input A,
  input B,
  input Cin,
  output Sum,
  output Cout
);

  assign Sum = A ^ B ^ Cin;
  assign Cout = (A & B) | (Cin & (A ^ B));
  
endmodule