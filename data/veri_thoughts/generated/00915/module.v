module full_adder(A, B, Ci, S, Co);
  input A, B, Ci;
  output S, Co;
  assign S = A ^ B ^ Ci;
  assign Co = (A & B) | (Ci & (A ^ B));
endmodule

module RCA_4(A, B, Ci, S, Co);
  input [3:0] A;
  input [3:0] B;
  input Ci;
  output [3:0] S;
  output Co;

  wire [3:1] CTMP;

  full_adder FAI_1(.A(A[0]), .B(B[0]), .Ci(Ci), .S(S[0]), .Co(CTMP[1]));
  full_adder FAI_2(.A(A[1]), .B(B[1]), .Ci(CTMP[1]), .S(S[1]), .Co(CTMP[2]));
  full_adder FAI_3(.A(A[2]), .B(B[2]), .Ci(CTMP[2]), .S(S[2]), .Co(CTMP[3]));
  full_adder FAI_4(.A(A[3]), .B(B[3]), .Ci(CTMP[3]), .S(S[3]), .Co(Co));
endmodule