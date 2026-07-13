
module CLK_GATE_MODULE (
  input CLK, EN, TE,
  output ENCLK
);

  assign ENCLK = (EN & ~TE) ? CLK & EN : 1'b0;

endmodule
