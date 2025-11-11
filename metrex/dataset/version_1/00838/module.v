
module my_module (i_0r0, i_0r1, i_0a, o_0r0, o_0r1, o_0a, reset);
  input i_0r0;
  input i_0r1;
  output i_0a;
  output o_0r0;
  output o_0r1;
  input o_0a;
  input reset;

  wire bna_0;
  wire tech1_oint;
  wire tech2_oint;
  wire bcomp_0;

  and (o_0r0, i_0r0, bna_0);
  nand (tech1_oint, o_0r0, reset);
  and (o_0r1, i_0r1, bna_0);
  nand (tech2_oint, o_0r1, reset);

  not (bna_0, o_0a);

  or (bcomp_0, o_0r0, o_0r1);
  buf (i_0a, bcomp_0);
endmodule
