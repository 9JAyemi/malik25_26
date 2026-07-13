module adder4bit ( A, B, Ci, S, Co );
  input [3:0] A, B;
  input Ci;
  output [3:0] S;
  output Co;
  wire c1, c2, c3;
  
  FA_1 fa1 ( .A(A[0]), .B(B[0]), .Ci(Ci), .S(S[0]), .Co(c1) );
  FA_1 fa2 ( .A(A[1]), .B(B[1]), .Ci(c1), .S(S[1]), .Co(c2) );
  FA_1 fa3 ( .A(A[2]), .B(B[2]), .Ci(c2), .S(S[2]), .Co(c3) );
  FA_1 fa4 ( .A(A[3]), .B(B[3]), .Ci(c3), .S(S[3]), .Co(Co) );
endmodule

module FA_1 ( A, B, Ci, S, Co );
  input A, B, Ci;
  output S, Co;
  wire n1, n2, n3;

  XOR2_X1 x1 ( .A(A), .B(B), .ZN(n1) );
  XOR2_X1 x2 ( .A(n1), .B(Ci), .ZN(S) );
  AND2_X1 a1 ( .A(A), .B(B), .ZN(n2) );
  AND2_X1 a2 ( .A(n1), .B(Ci), .ZN(n3) );
  OR2_X1 o1 ( .A(n2), .B(n3), .ZN(Co) );
endmodule

module XOR2_X1 ( A, B, ZN );
  input A, B;
  output ZN;
  assign ZN = A ^ B;
endmodule

module AND2_X1 ( A, B, ZN );
  input A, B;
  output ZN;
  assign ZN = A & B;
endmodule

module OR2_X1 ( A, B, ZN );
  input A, B;
  output ZN;
  assign ZN = A | B;
endmodule