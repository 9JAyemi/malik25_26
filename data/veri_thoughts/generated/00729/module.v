
module add8(X, Y, S, Cout);
  input [7:0] X, Y;
  output [7:0] S;
  output Cout;

  wire [3:0] A, B, C;

  adder_4bit inst1(.A(X[3:0]), .B(Y[3:0]), .S(S[3:0]), .Cout(C[0]));
  adder_4bit inst2(.A(X[7:4]), .B(Y[7:4]), .S(S[7:4]), .Cin(C[0]), .Cout(Cout));

endmodule

module adder_4bit(A, B, S, Cin, Cout);
  input [3:0] A, B;
  output [3:0] S;
  input Cin;
  output Cout;

  wire [2:0] C;

  full_adder inst1(.A(A[0]), .B(B[0]), .Cin(Cin), .S(S[0]), .Cout(C[0]));
  full_adder inst2(.A(A[1]), .B(B[1]), .Cin(C[0]), .S(S[1]), .Cout(C[1]));
  full_adder inst3(.A(A[2]), .B(B[2]), .Cin(C[1]), .S(S[2]), .Cout(C[2]));
  full_adder inst4(.A(A[3]), .B(B[3]), .Cin(C[2]), .S(S[3]), .Cout(Cout));

endmodule

module full_adder(A, B, Cin, S, Cout);
  input A, B, Cin;
  output S, Cout;

  assign S = A ^ B ^ Cin;
  assign Cout = (A & B) | (B & Cin) | (A & Cin);

endmodule
