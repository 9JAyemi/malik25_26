
module FullAdder(input a,b,c, output sum, carry);
  wire s1, c1, c2;
  xor g1(s1, a, b);
  xor g2(sum, s1, c);
  and g3(c1, a, b);
  and g4(c2, s1, c);
  xor g5(carry, c1, c2);
endmodule

module RippleCarryAdder(input [3:0] A, input [3:0] B, output [3:0] S, output Cout);

  wire c1, c2, c3;

  FullAdder fa1(A[0], B[0], 0, S[0], c1);
  FullAdder fa2(A[1], B[1], c1, S[1], c2);
  FullAdder fa3(A[2], B[2], c2, S[2], c3);
  FullAdder fa4(A[3], B[3], c3, S[3], Cout);

endmodule
