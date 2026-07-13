
module four_bit_adder(A, B, C_in, S, C_out);
  input [3:0] A;
  input [3:0] B;
  input C_in;
  output [3:0] S;
  output C_out;

  wire c1, c2, c3;

  assign {c1, S[0]} = A[0] + B[0] + C_in;
  assign {c3, S[1]} = A[1] + B[1] + c1;
  assign {c2, S[2]} = A[2] + B[2] + c3;
  assign {C_out, S[3]} = A[3] + B[3] + c2;

endmodule