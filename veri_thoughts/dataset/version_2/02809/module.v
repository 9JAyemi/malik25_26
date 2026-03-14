
module SNPS_CLOCK_GATE_HIGH_RegisterAdd_W48 ( CLK, EN, ENCLK, TE );
  input CLK, EN, TE;
  output ENCLK;
  
  reg gated_clk;
  
  always @ (posedge CLK)
    if (EN && !TE)
      gated_clk <= 1'b1;
    else
      gated_clk <= 1'b0;
  
  TLATCH latch ( .E(EN), .SE(TE), .CK(gated_clk), .ECK(ENCLK) );
endmodule
module TLATCH ( E, SE, CK, ECK );
  input E, SE, CK;
  output ECK;
  
  reg eck;
  
  always @ (posedge CK or posedge SE)
    if (SE)
      eck <= 1'b0;
    else
      eck <= E;
    
  assign ECK = eck;
endmodule