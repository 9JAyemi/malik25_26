
module adder_N4_14 ( A, B, Ci, S, Co );
  input [3:0] A;
  input [3:0] B;
  output [3:0] S;
  input Ci;
  output Co;

  wire   [3:0] nocarry_sum_to_mux;
  wire   [3:0] carry_sum_to_mux;

  RCA_N4_29 rca_nocarry ( .A(A), .B(B), .Ci(1'b0), .S(nocarry_sum_to_mux) );
  RCA_N4_28 rca_carry ( .A(A), .B(B), .Ci(1'b1), .S(carry_sum_to_mux) );
  mux21_SIZE4 mux21 ( .IN0(nocarry_sum_to_mux), .IN1(carry_sum_to_mux), 
        .CTRL(Ci), .OUT1(S) );
  assign Co = carry_sum_to_mux[3];
endmodule
module RCA_N4_28 ( A, B, Ci, S );
  input [3:0] A;
  input [3:0] B;
  input Ci;
  output [3:0] S;

  wire   [3:0] cout;

  FA FA0 ( .A(A[0]), .B(B[0]), .Ci(Ci), .S(S[0]), .Co(cout[0]) );
  FA FA1 ( .A(A[1]), .B(B[1]), .Ci(cout[0]), .S(S[1]), .Co(cout[1]) );
  FA FA2 ( .A(A[2]), .B(B[2]), .Ci(cout[1]), .S(S[2]), .Co(cout[2]) );
  FA FA3 ( .A(A[3]), .B(B[3]), .Ci(cout[2]), .S(S[3]), .Co(cout[3]) );
endmodule
module RCA_N4_29 ( A, B, Ci, S );
  input [3:0] A;
  input [3:0] B;
  input Ci;
  output [3:0] S;

  wire   [3:0] cout;

  FA FA0 ( .A(A[0]), .B(B[0]), .Ci(Ci), .S(S[0]), .Co(cout[0]) );
  FA FA1 ( .A(A[1]), .B(B[1]), .Ci(cout[0]), .S(S[1]), .Co(cout[1]) );
  FA FA2 ( .A(A[2]), .B(B[2]), .Ci(cout[1]), .S(S[2]), .Co(cout[2]) );
  FA FA3 ( .A(A[3]), .B(B[3]), .Ci(cout[2]), .S(S[3]), .Co(cout[3]) );
endmodule
module FA ( A, B, Ci, S, Co );
  input A, B, Ci;
  output S, Co;
  assign S   = A ^ B ^ Ci;
  assign Co   = (A & B) | (A & Ci) | (B & Ci);
endmodule
module mux21_SIZE4 ( IN0, IN1, CTRL, OUT1);
   parameter SIZE = 4 ;
   input [SIZE - 1 :0] IN0;
   input [SIZE - 1 :0] IN1;
   input   CTRL;
   output  [SIZE - 1 :0] OUT1 ;
   assign OUT1 = ( CTRL == 1'b0 )? IN0: IN1;
endmodule