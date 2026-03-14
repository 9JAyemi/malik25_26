
module SNPS_CLOCK_GATE_HIGH_RegisterAdd_W26_1_3 (EN, TE, CLK, ENCLK);
  input EN, TE, CLK;
  output ENCLK;

  assign ENCLK = EN && TE && CLK;

endmodule
