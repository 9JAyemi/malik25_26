module adder4bit(
  input [3:0] A, B,
  input Cin,
  output [3:0] S,
  output Cout
  );

  wire [3:0] sum;
  wire C1, C2, C3;

  // Full adder for bit 0
  full_adder fa0(A[0], B[0], Cin, sum[0], C1);

  // Full adder for bit 1
  full_adder fa1(A[1], B[1], C1, sum[1], C2);

  // Full adder for bit 2
  full_adder fa2(A[2], B[2], C2, sum[2], C3);

  // Full adder for bit 3
  full_adder fa3(A[3], B[3], C3, sum[3], Cout);

  assign S = sum;

endmodule

module full_adder(
  input A, B, Cin,
  output S, Cout
  );

  assign S = A ^ B ^ Cin;
  assign Cout = (A & B) | (Cin & (A ^ B));

endmodule