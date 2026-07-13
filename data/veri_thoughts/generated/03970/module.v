
module clock_gating (CLK, EN, TE, ENCLK);
  input CLK, EN, TE;
  output ENCLK;

  reg ENCLK;

  always @(posedge CLK)
    if (EN & TE)
      ENCLK <= 1'b1;
    else
      ENCLK <= 1'b0;

endmodule
