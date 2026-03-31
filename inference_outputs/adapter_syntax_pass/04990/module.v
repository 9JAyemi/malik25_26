module ripple_carry_adder (
  input [3:0] A,
  input [3:0] B,
  input cin,
  output [3:0] sum,
  output cout
);

  wire [3:0] carry;
  full_adder FA0 (A[0], B[0], cin, sum[0], carry[0]);
  full_adder FA1 (A[1], B[1], carry[0], sum[1], carry[1]);
  full_adder FA2 (A[2], B[2], carry[1], sum[2], carry[2]);
  full_adder FA3 (A[3], B[3], carry[2], sum[3], cout);

endmodule
module full_adder (
  input a,
  input b,
  input cin,
  output sum,
  output cout
);

  assign sum = a ^ b ^ cin;
  assign cout = (a & b) | (a & cin) | (b & cin);

endmodule
