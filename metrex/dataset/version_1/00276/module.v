
module RippleCarryAdder(S, Cout, A, B, Cin);
  input [3:0] A;
  input [3:0] B;
  input Cin;
  output [3:0] S;
  output Cout;

  wire [3:0] w1;
  wire [3:0] w2;
  wire [3:0] w3;

  FA FA0(w1[0], w2[0], A[0], B[0], Cin);
  FA FA1(w1[1], w2[1], A[1], B[1], w2[0]);
  FA FA2(w1[2], w2[2], A[2], B[2], w2[1]);
  FA FA3(Cout, w1[3], A[3], B[3], w2[2]);

  assign S = w1;
endmodule
module FA(S, Cout, A, B, Cin);
  input A, B, Cin;
  output S, Cout;

  assign {Cout, S} = A + B + Cin;
endmodule