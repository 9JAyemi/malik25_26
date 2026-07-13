
module FullAdder(A, B, Ci, S, Co);
  input A, B, Ci;
  output S, Co;
  wire n1, n2, n3;

  xor (n1, A, B);
  xor (S, n1, Ci);
  and (n2, A, B);
  and (n3, n1, Ci);
  or (Co, n2, n3);
endmodule
module Mux1(A, B, Sel, Out);
  input A, B, Sel;
  output Out;

  assign Out = (Sel) ? A : B;
endmodule
module Mux4bit(A, B, Sel, Out);
  input [3:0] A, B;
  input Sel;
  output [3:0] Out;

  assign Out = (Sel) ? A : B;
endmodule
module RippleCarryAdder4bit(A, B, Ci, S, Co);
  input [3:0] A, B;
  input Ci;
  output [3:0] S;
  output Co;

  wire [3:0] c;

  FullAdder FA1 ( .A(A[0]), .B(B[0]), .Ci(Ci), .S(S[0]), .Co(c[0]) );
  FullAdder FA2 ( .A(A[1]), .B(B[1]), .Ci(c[0]), .S(S[1]), .Co(c[1]) );
  FullAdder FA3 ( .A(A[2]), .B(B[2]), .Ci(c[1]), .S(S[2]), .Co(c[2]) );
  FullAdder FA4 ( .A(A[3]), .B(B[3]), .Ci(c[2]), .S(S[3]), .Co(Co) );
endmodule
module Adder4bit(A, B, S, Co);
  input [3:0] A, B;
  output [3:0] S;
  output Co;

  wire c;

  RippleCarryAdder4bit RCA ( .A(A), .B(B), .Ci(1'b0), .S(S), .Co(c) );
  assign Co = c;
endmodule