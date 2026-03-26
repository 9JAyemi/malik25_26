
module adder_subtractor (
    input [3:0] A,
    input [3:0] B,
    input C,
    output [3:0] Y
);

  wire [3:0] A_inv;
  wire [3:0] B_inv;
  wire [3:0] carry_in;
  wire [3:0] carry_out;

  assign A_inv = ~A;
  assign B_inv = ~B;
  assign carry_in[0] = C;
  assign carry_in[1] = C & A_inv[0];
  assign carry_in[2] = C & A_inv[1] & A_inv[0];
  assign carry_in[3] = C & A_inv[2] & A_inv[1] & A_inv[0];
  assign carry_out[0] = carry_in[0] & B[0];
  assign carry_out[1] = carry_in[1] & B[1];
  assign carry_out[2] = carry_in[2] & B[2];
  assign carry_out[3] = carry_in[3] & B[3];

  assign Y[0] = A[0] ^ B[0] ^ carry_out[0];
  assign Y[1] = A[1] ^ B[1] ^ carry_out[1];
  assign Y[2] = A[2] ^ B[2] ^ carry_out[2];
  assign Y[3] = A[3] ^ B[3] ^ carry_out[3];

endmodule