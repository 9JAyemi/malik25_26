
module Adder4(
    input [3:0] A,
    input [3:0] B,
    output [4:0] S
);

  wire [0:0] Q1, Q2, Q3, Q4, Q5;
  wire [0:0] ready_add_subt1, ready_add_subt2, ready_add_subt3, ready_add_subt4;

  Adder Sub1(A[0], B[0], ready_add_subt1, Q1, ready_add_subt2);
  Adder Sub2(A[1], B[1], ready_add_subt2, Q2, ready_add_subt3);
  Adder Sub3(A[2], B[2], ready_add_subt3, Q3, ready_add_subt4);
  Adder Sub4(A[3], B[3], ready_add_subt4, Q4, S[4]);

  assign S[0] = Q1;
  assign S[1] = Q2;
  assign S[2] = Q3;
  assign S[3] = Q4;

  assign ready_add_subt1 = 1'b1;

endmodule

module Adder(
    input A,
    input B,
    input Cin,
    output S,
    output ready_add_subt
);

  wire Cn;

  xor (S, A, B);
  xor (Cn, S, Cin);
  not (ready_add_subt, Cn);

endmodule
