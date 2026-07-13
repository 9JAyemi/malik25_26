module pg_45 ( g, p, g_prec, p_prec, p_out, g_out_BAR );
  input g, p, g_prec, p_prec;
  output p_out, g_out_BAR;

  // AOI21 gate
  wire g_out_BAR_wire;
  assign g_out_BAR_wire = ~(g_prec & p | g);
  assign g_out_BAR = g_out_BAR_wire;

  // AND2 gate
  wire p_out_wire;
  assign p_out_wire = p_prec & p;
  assign p_out = p_out_wire;

endmodule