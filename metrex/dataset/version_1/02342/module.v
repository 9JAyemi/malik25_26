
module full_adder(a, b, c_in, s, c_out);
  input a, b, c_in;
  output s, c_out;
  assign s = a ^ b ^ c_in;
  assign c_out = (a & b) | (b & c_in) | (c_in & a);
endmodule

module four_bit_adder(A, B, C_in, S, C_out);
  input [3:0] A, B;
  input C_in;
  output [3:0] S;
  output C_out;

  wire c1, c2, c3;

  full_adder adder0(A[0], B[0], C_in, S[0], c1);
  full_adder adder1(A[1], B[1], c1, S[1], c2);
  full_adder adder2(A[2], B[2], c2, S[2], c3);
  full_adder adder3(A[3], B[3], c3, S[3], C_out);
endmodule
