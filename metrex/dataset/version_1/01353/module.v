module four_bit_adder(
  input [3:0] A, B,
  input Cin,
  output [3:0] S,
  output Cout
);

  wire C1, C2, C3;
  full_adder FA1(S[0], C1, A[0], B[0], Cin);
  full_adder FA2(S[1], C2, A[1], B[1], C1);
  full_adder FA3(S[2], C3, A[2], B[2], C2);
  full_adder FA4(S[3], Cout, A[3], B[3], C3);

endmodule

module full_adder(
  output sum,
  output carry_out,
  input A,
  input B,
  input carry_in
);

  assign {carry_out, sum} = A + B + carry_in;

endmodule