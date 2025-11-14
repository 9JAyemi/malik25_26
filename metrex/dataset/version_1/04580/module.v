
module addsub(
  input [3:0] A,
  input [3:0] B,
  input M,
  output [3:0] R,
  output COUT,
  output V
);

  wire [4:0] temp;
  wire [3:0] B_neg;
  wire [3:0] two_comp;

  assign temp = A + (M ? ~B + 1'b1 : B);
  assign B_neg = (M ? ~B + 1'b1 : B);
  assign two_comp = (M ? {~temp[4], temp[3:0]} : temp[3:0]);

  assign R = (M ? two_comp : temp[3:0]);
  assign COUT = temp[4] ^ M;
  assign V = (A[3] == B[3] && R[3] != A[3]) ? 1'b1 : 1'b0;

endmodule
