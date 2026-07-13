module RCA_4bit (
  input [3:0] A,
  input [3:0] B,
  output [3:0] S,
  input Ci,
  output Co
);

  wire [3:1] CTMP;

  FA_1 FAI_1 ( .A(A[0]), .B(B[0]), .Ci(Ci), .S(S[0]), .Co(CTMP[1]) );
  FA_1 FAI_2 ( .A(A[1]), .B(B[1]), .Ci(CTMP[1]), .S(S[1]), .Co(CTMP[2]) );
  FA_1 FAI_3 ( .A(A[2]), .B(B[2]), .Ci(CTMP[2]), .S(S[2]), .Co(CTMP[3]) );
  FA_1 FAI_4 ( .A(A[3]), .B(B[3]), .Ci(CTMP[3]), .S(S[3]), .Co(Co) );

endmodule

module FA_1 (
  input A,
  input B,
  input Ci,
  output S,
  output Co
);

  assign {Co, S} = A + B + Ci;

endmodule