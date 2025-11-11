
module state_module ( g, p, g_prec, p_prec, g_out, p_out );
  input g, p, g_prec, p_prec;
  output g_out, p_out;
  wire   n5, p_prec_inv;

  // Inverting p_prec
  not U4 ( p_prec_inv, p_prec);

  // AND-OR-INVERT gate
  and ( n5, p_prec_inv, g_prec);
  or ( g_out, p, n5);

  // AND gate
  and ( p_out, p, p_prec);
endmodule