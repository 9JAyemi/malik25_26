module four_bit_adder(
  input [3:0] A,
  input [3:0] B,
  input CIN,
  output [3:0] SUM,
  output COUT,
  input VPWR,
  input VGND
);

  wire [3:0] C;
  wire [3:0] S;

  assign S[0] = A[0] ^ B[0] ^ CIN;
  assign C[0] = (A[0] & B[0]) | (A[0] & CIN) | (B[0] & CIN);

  assign S[1] = A[1] ^ B[1] ^ C[0];
  assign C[1] = (A[1] & B[1]) | (A[1] & C[0]) | (B[1] & C[0]);

  assign S[2] = A[2] ^ B[2] ^ C[1];
  assign C[2] = (A[2] & B[2]) | (A[2] & C[1]) | (B[2] & C[1]);

  assign S[3] = A[3] ^ B[3] ^ C[2];
  assign COUT = (A[3] & B[3]) | (A[3] & C[2]) | (B[3] & C[2]);

  assign SUM = {S[3], S[2], S[1], S[0]};
  
endmodule