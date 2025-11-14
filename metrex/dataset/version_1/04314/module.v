module SNPS_CLOCK_GATE_HIGH_RegisterAdd_W6_87 ( CLK, EN, TE, ENCLK );
  input CLK, EN, TE;
  output ENCLK;

  assign ENCLK = (EN | TE) ? CLK : 1'b0;

endmodule