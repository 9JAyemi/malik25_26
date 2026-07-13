
module ripple_carry_adder(
  input [3:0] A, B,
  input Cin,
  output [3:0] Sum,
  output Cout
);

  wire [3:0] c;
  wire [3:0] s;

  half_adder ha0(.COUT(c[0]), .SUM(s[0]), .A(A[0]), .B(B[0]));
  half_adder ha1(.COUT(c[1]), .SUM(s[1]), .A(A[1]), .B(B[1]), .CIN(c[0]));
  half_adder ha2(.COUT(c[2]), .SUM(s[2]), .A(A[2]), .B(B[2]), .CIN(c[1]));
  half_adder ha3(.COUT(Cout), .SUM(s[3]), .A(A[3]), .B(B[3]), .CIN(c[2]));

  assign Sum = s;

endmodule

module half_adder(
  input A, B, CIN,
  output COUT, SUM
);

  assign SUM = A ^ B ^ CIN;
  assign COUT = (A & B) | (A & CIN) | (B & CIN);

endmodule
