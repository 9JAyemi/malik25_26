module pg_5 ( g, p, g_prec, p_prec, g_out, p_out );
  input g, p, g_prec, p_prec;
  output g_out, p_out;
  wire   n5, n6;

  and U1 (p_out, p, p_prec);
  not U2 (n6, g);
  nand U3 (n5, p, g_prec);
  nand U4 (g_out, n5, n6);
endmodule