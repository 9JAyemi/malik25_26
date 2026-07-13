module pg_51 ( g, p, g_prec, p_prec, p_out, g_out_BAR );
  input g, p, g_prec, p_prec;
  output p_out, g_out_BAR;

  // AOI21 gate implementation
  wire aoi_out;
  assign aoi_out = ~(g_prec & p & g);

  // AND2 gate implementation
  wire and_out;
  assign and_out = p & p_prec;

  // Output assignments
  assign p_out = and_out;
  assign g_out_BAR = aoi_out;
endmodule