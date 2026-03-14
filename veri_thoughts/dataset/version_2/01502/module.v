module ripple_carry_adder (
  input [3:0] A,
  input [3:0] B,
  input carry_in,
  output [3:0] sum,
  output carry_out
);

  wire [3:0] carry;
  
  full_adder FA0(A[0], B[0], carry_in, sum[0], carry[0]);
  full_adder FA1(A[1], B[1], carry[0], sum[1], carry[1]);
  full_adder FA2(A[2], B[2], carry[1], sum[2], carry[2]);
  full_adder FA3(A[3], B[3], carry[2], sum[3], carry_out);
  
endmodule
module full_adder (
  input A,
  input B,
  input C_in,
  output S,
  output C_out
);

  assign S = A ^ B ^ C_in;
  assign C_out = (A & B) | (C_in & (A ^ B));
  
endmodule
