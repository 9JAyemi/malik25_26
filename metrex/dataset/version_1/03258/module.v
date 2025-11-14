
module four_bit_adder(
  input [3:0] A,
  input [3:0] B,
  input Cin,
  output [3:0] S,
  output Cout
);

  wire [3:0] carry;

  // Full adder for bit 0
  full_adder fa0 (.a(A[0]), .b(B[0]), .cin(Cin), .sum(S[0]), .cout(carry[0]));
  
  // Full adder for bit 1
  full_adder fa1 (.a(A[1]), .b(B[1]), .cin(carry[0]), .sum(S[1]), .cout(carry[1]));
  
  // Full adder for bit 2
  full_adder fa2 (.a(A[2]), .b(B[2]), .cin(carry[1]), .sum(S[2]), .cout(carry[2]));
  
  // Full adder for bit 3
  full_adder fa3 (.a(A[3]), .b(B[3]), .cin(carry[2]), .sum(S[3]), .cout(Cout));

endmodule
module full_adder(
  input a,
  input b,
  input cin,
  output sum,
  output cout
);

  assign {cout, sum} = a + b + cin;

endmodule