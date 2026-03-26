
module adder(
  input [3:0] A,
  input [3:0] B,
  input Cin,
  output [3:0] Sum,
  output Cout
);

  wire [3:0] temp_sum;
  wire c1, c2, c3;

  full_adder fa1(.A(A[0]), .B(B[0]), .Cin(Cin), .Sum(temp_sum[0]), .Cout(c1));
  full_adder fa2(.A(A[1]), .B(B[1]), .Cin(c1), .Sum(temp_sum[1]), .Cout(c2));
  full_adder fa3(.A(A[2]), .B(B[2]), .Cin(c2), .Sum(temp_sum[2]), .Cout(c3));
  full_adder fa4(.A(A[3]), .B(B[3]), .Cin(c3), .Sum(Sum[3]), .Cout(Cout));

  assign Sum[2] = temp_sum[2];
  assign Sum[1] = temp_sum[1];
  assign Sum[0] = temp_sum[0];

endmodule
module full_adder(
  input A,
  input B,
  input Cin,
  output Sum,
  output Cout
);

  assign Sum = A ^ B ^ Cin;
  assign Cout = (A & B) | (A & Cin) | (B & Cin);

endmodule