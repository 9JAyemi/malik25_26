
module tkl5x1 (i_0r0, i_0r1, i_0a, o_0r0, o_0r1, o_0a, reset);
  input [4:0] i_0r0;
  input [4:0] i_0r1;
  input i_0a;
  output [4:0] o_0r0;
  output [4:0] o_0r1;
  output o_0a;
  input reset;

  wire bna_0;
  wire tech1_oint;
  wire tech2_oint;
  wire tech3_oint;
  wire tech4_oint;
  wire tech5_oint;
  wire tech6_oint;
  wire tech7_oint;
  wire tech8_oint;
  wire tech9_oint;
  wire tech10_oint;
  wire [4:0] bcomp_0;
  wire [1:0] simp181_0;
  wire tech19_int;

  assign o_0r0 = i_0r0 | (i_0r1 & i_0a);
  assign o_0r1 = i_0r0 | (i_0r1 & i_0a);
  assign bcomp_0 = o_0r0 | o_0r1;
  assign simp181_0 = bcomp_0[1:0] & bcomp_0[3:2];
  assign tech19_int = bcomp_0[4] | bcomp_0[2:1];
  assign o_0a = simp181_0[0] & simp181_0[1];
endmodule