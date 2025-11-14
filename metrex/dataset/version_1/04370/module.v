
module mux21_SIZE4_3 ( IN0, IN1, CTRL, OUT1 );
  input [3:0] IN0;
  input [3:0] IN1;
  output [3:0] OUT1;
  input CTRL;

  wire [3:0] mux1_out;
  wire [3:0] mux2_out;
  wire [3:0] mux3_out;
  wire [3:0] mux4_out;

  MUX2_X1 U1 ( .A(IN0[3]), .B(IN1[3]), .S(CTRL), .Z(mux1_out[3]) );
  MUX2_X1 U2 ( .A(IN0[2]), .B(IN1[2]), .S(CTRL), .Z(mux2_out[2]) );
  MUX2_X1 U3 ( .A(IN0[1]), .B(IN1[1]), .S(CTRL), .Z(mux3_out[1]) );
  MUX2_X1 U4 ( .A(IN0[0]), .B(IN1[0]), .S(CTRL), .Z(mux4_out[0]) );

  assign OUT1 = {mux1_out[3], mux2_out[2], mux3_out[1], mux4_out[0]};
endmodule
module MUX2_X1 ( A, B, S, Z );
  input A, B, S;
  output Z;

  assign Z = (S == 0)? A : B;
endmodule