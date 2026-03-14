module SNPS_CLOCK_GATE_HIGH_RegisterAdd_W17 ( CLK, EN, ENCLK, TE );
  input CLK, EN, TE;
  output ENCLK;

  TLATNTSCAX2TS latch ( .E(EN), .SE(TE), .CK(CLK), .ECK(ENCLK) );
  
endmodule

module TLATNTSCAX2TS ( E, SE, CK, ECK );
  input E, SE, CK;
  output reg ECK;

  always @ (posedge CK)
    if (E) ECK <= SE;

endmodule