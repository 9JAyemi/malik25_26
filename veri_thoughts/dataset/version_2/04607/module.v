module g_17 ( g, p, g_prec, g_out );
  input g, p, g_prec;
  output g_out;
  wire n2;

  AOI21_X1 U2 ( .B1(p), .B2(g_prec), .A(g), .ZN(n2) );
  INV_X1 U1 ( .A(n2), .ZN(g_out) );
endmodule

module AOI21_X1 (B1, B2, A, ZN);
  input B1, B2, A;
  output ZN;
  assign ZN = ~(B1 & B2 & A);
endmodule

module INV_X1 (A, ZN);
  input A;
  output ZN;
  assign ZN = ~A;
endmodule