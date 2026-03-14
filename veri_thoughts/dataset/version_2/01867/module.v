module g_18 ( g, p, g_prec, g_out );
  input g, p;
  input [1:0] g_prec;
  output g_out;
  wire n2;

  // AOI21 gate
  assign n2 = ~(p & g_prec[1] & ~g);

  // Inverter gate
  assign g_out = ~n2;
endmodule