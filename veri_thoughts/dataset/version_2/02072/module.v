module muddlib07__nand2_1x(a, b, y);
  input a, b;
  output y;
  assign y = ~(a & b);
endmodule

module muddlib07__xor2_1x(a, b, y);
  input a, b;
  output y;
  assign y = a ^ b;
endmodule

module wordlib8__PPGen_1bit(Double, Negate, Single, Yi, Yi_m1, PPi);
  input Double;
  input Negate;
  input Single;
  input Yi;
  input Yi_m1;
  output PPi;

  supply1 vdd;
  supply0 gnd;
  wire net_0, net_2, net_4;

  muddlib07__nand2_1x nand2_1x_0(.a(Single), .b(Yi), .y(net_0));
  muddlib07__nand2_1x nand2_1x_1(.a(net_0), .b(net_2), .y(net_4));
  muddlib07__nand2_1x nand2_1x_2(.a(Double), .b(Yi_m1), .y(net_2));
  muddlib07__xor2_1x xor2_1x_0(.a(net_4), .b(Negate), .y(PPi));
endmodule