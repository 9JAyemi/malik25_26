
module four_bit_adder ( A, B, Ci, S, Co );
  input [3:0] A, B;
  input Ci;
  output [3:0] S;
  output Co;
  wire [3:0] n1;
  wire n5, n6, n7;

  // First full adder
  full_adder fa1 ( .A(A[0]), .B(B[0]), .Ci(Ci), .S(n1[0]), .Co(n5) );

  // Second full adder
  full_adder fa2 ( .A(A[1]), .B(B[1]), .Ci(n5), .S(n1[1]), .Co(n6) );

  // Third full adder
  full_adder fa3 ( .A(A[2]), .B(B[2]), .Ci(n6), .S(n1[2]), .Co(n7) );

  // Fourth full adder
  full_adder fa4 ( .A(A[3]), .B(B[3]), .Ci(n7), .S(n1[3]), .Co(Co) );

  assign S = n1;
endmodule
module full_adder ( A, B, Ci, S, Co );
  input A, B, Ci;
  output S, Co;
  wire n1, n2, n3;

  assign n1 = A ^ B;
  assign S = n1 ^ Ci;
  assign n2 = A & B;
  assign n3 = n1 & Ci;
  assign Co = n2 | n3;
endmodule