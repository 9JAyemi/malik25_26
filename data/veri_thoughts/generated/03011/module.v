module clock_gate(
  input CLK, EN, TE,
  output ENCLK
);

  wire gated_clk;

  assign gated_clk = (EN & ~TE) ? CLK : 1'b0;
  assign ENCLK = (EN) ? gated_clk : 1'b0;

endmodule