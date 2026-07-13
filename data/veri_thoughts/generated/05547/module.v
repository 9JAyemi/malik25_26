module SNPS_CLOCK_GATE_HIGH_RegisterMult_W24 ( CLK, EN, ENCLK, TE );
  input CLK, EN, TE;
  output ENCLK;

  assign ENCLK = (EN == 1'b1 && TE == 1'b1) ? CLK : 1'b0;

endmodule