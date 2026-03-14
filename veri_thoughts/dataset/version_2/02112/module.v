module logic_module (a, b, g_out, p_out);
  input a, b;
  output g_out, p_out;
  wire n2;

  not inv1 (n2, a);
  and (g_out, a, b);
  xnor (p_out, b, n2);

endmodule