
module mod ( A, Z );
  input [7:0] A;
  output Z;

  mod5 U98 ( .Z(Z), .A(A[4:0]) );

endmodule
module mod5 ( A, Z );
  input [4:0] A;
  output Z;

  assign Z = (A % 5 == 0) ? 1 : 0;

endmodule