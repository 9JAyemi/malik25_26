module adder4(
  input [3:0] A,
  input [3:0] B,
  output [3:0] O,
  output C
);

  wire [3:0] sum;
  wire carry1, carry2, carry3;

  // First adder stage
  full_adder FA1(.A(A[0]), .B(B[0]), .Cin(1'b0), .S(sum[0]), .Cout(carry1));

  // Second adder stage
  full_adder FA2(.A(A[1]), .B(B[1]), .Cin(carry1), .S(sum[1]), .Cout(carry2));

  // Third adder stage
  full_adder FA3(.A(A[2]), .B(B[2]), .Cin(carry2), .S(sum[2]), .Cout(carry3));

  // Fourth adder stage
  full_adder FA4(.A(A[3]), .B(B[3]), .Cin(carry3), .S(sum[3]), .Cout(C));

  assign O = sum;

endmodule

module full_adder(
  input A,
  input B,
  input Cin,
  output S,
  output Cout
);

  assign S = A ^ B ^ Cin;
  assign Cout = (A & B) | (A & Cin) | (B & Cin);

endmodule