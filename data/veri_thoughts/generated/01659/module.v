
module INV_X1 (A, ZN);
  input A;
  output ZN;
  
  assign ZN = ~A;
endmodule
module NAND2_X1 (A1, A2, ZN);
  input A1, A2;
  output ZN;
  
  assign ZN = ~(A1 & A2);
endmodule
module g_3 (g, p, g_prec, g_out);
  input g, p, g_prec;
  output g_out;
  wire n5, n6;
  
  INV_X1 U1 (.A(g), .ZN(n6));
  NAND2_X1 U2 (.A1(n5), .A2(n6), .ZN(g_out));
  NAND2_X1 U3 (.A1(g_prec), .A2(p), .ZN(n5));
  
endmodule