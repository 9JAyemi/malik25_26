module RCA_N4_17 ( A, B, Ci, S, Co );
  input [3:0] A;
  input [3:0] B;
  output [3:0] S;
  input Ci;
  output Co;

  wire   [3:1] CTMP;

  FA_71 FAI_1 ( .A(A[0]), .B(B[0]), .Ci(Ci), .S(S[0]), .Co(CTMP[1]) );
  FA_70 FAI_2 ( .A(A[1]), .B(B[1]), .Ci(CTMP[1]), .S(S[1]), .Co(CTMP[2]) );
  FA_69 FAI_3 ( .A(A[2]), .B(B[2]), .Ci(CTMP[2]), .S(S[2]), .Co(CTMP[3]) );
  FA_68 FAI_4 ( .A(A[3]), .B(B[3]), .Ci(CTMP[3]), .S(S[3]), .Co(Co) );
  
endmodule

module FA_71 ( A, B, Ci, S, Co );
  input A, B, Ci;
  output S, Co;
  assign S = A ^ B ^ Ci;
  assign Co = (A & B) | (A & Ci) | (B & Ci);
endmodule

module FA_70 ( A, B, Ci, S, Co );
  input A, B, Ci;
  output S, Co;
  assign S = A ^ B ^ Ci;
  assign Co = (A & B) | (A & Ci) | (B & Ci);
endmodule

module FA_69 ( A, B, Ci, S, Co );
  input A, B, Ci;
  output S, Co;
  assign S = A ^ B ^ Ci;
  assign Co = (A & B) | (A & Ci) | (B & Ci);
endmodule

module FA_68 ( A, B, Ci, S, Co );
  input A, B, Ci;
  output S, Co;
  assign S = A ^ B ^ Ci;
  assign Co = (A & B) | (A & Ci) | (B & Ci);
endmodule