module full_adder (
  input A,
  input B,
  input C_in,
  output Sum,
  output C_out
);

  assign Sum = A ^ B ^ C_in;
  assign C_out = (A & B) | (C_in & (A ^ B));

endmodule

module ripple_carry_adder (
  input [3:0] A,
  input [3:0] B,
  input C_in,
  output [3:0] Sum,
  output C_out
);

  wire [3:0] carry;
  full_adder fa0(A[0], B[0], C_in, Sum[0], carry[0]);
  full_adder fa1(A[1], B[1], carry[0], Sum[1], carry[1]);
  full_adder fa2(A[2], B[2], carry[1], Sum[2], carry[2]);
  full_adder fa3(A[3], B[3], carry[2], Sum[3], C_out);

endmodule