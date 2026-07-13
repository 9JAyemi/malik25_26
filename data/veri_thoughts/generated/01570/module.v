
module and_xnor_inv (
  input a,
  input b,
  output g_out,
  output p_out
);

  wire n3;

  // Inverter
  not (n3, a);

  // AND gate
  and (g_out, a, b);

  // XNOR gate
  xnor (p_out, n3, b);

endmodule
