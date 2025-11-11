module full_adder (
  input A,
  input B,
  input Cin,
  output reg S,
  output reg Cout
);

  always @ (A, B, Cin) begin
    S = A ^ B ^ Cin;
    Cout = (A & B) | (Cin & (A ^ B));
  end

endmodule


module four_bit_adder (
  input [3:0] A,
  input [3:0] B,
  input Cin,
  output [3:0] S,
  output Cout
);

  wire c1, c2, c3;
  full_adder fa1(A[0], B[0], Cin, S[0], c1);
  full_adder fa2(A[1], B[1], c1, S[1], c2);
  full_adder fa3(A[2], B[2], c2, S[2], c3);
  full_adder fa4(A[3], B[3], c3, S[3], Cout);

endmodule