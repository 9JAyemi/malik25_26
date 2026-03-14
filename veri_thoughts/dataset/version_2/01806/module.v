
module four_bit_adder_structural (
  input [3:0] A,
  input [3:0] B,
  output [3:0] S
);

  wire c0, c1, c2;
  full_adder FA0(.a(A[0]), .b(B[0]), .cin(1'b0), .sum(S[0]), .cout(c0));
  full_adder FA1(.a(A[1]), .b(B[1]), .cin(c0), .sum(S[1]), .cout(c1));
  full_adder FA2(.a(A[2]), .b(B[2]), .cin(c1), .sum(S[2]), .cout(c2));
  full_adder FA3(.a(A[3]), .b(B[3]), .cin(c2), .sum(S[3]), .cout());

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
