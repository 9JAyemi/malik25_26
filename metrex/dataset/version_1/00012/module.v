
module TLATNTSCAX2TS (E, SE, CK, ECK);
  input E, SE, CK;
  output ECK;

  assign ECK = E & SE & CK;
endmodule

module SNPS_CLOCK_GATE_HIGH_RegisterAdd_W24 ( CLK, EN, TE, ENCLK );
  input CLK, EN, TE;
  output ENCLK;

  TLATNTSCAX2TS latch ( .E(EN), .SE(TE), .CK(CLK), .ECK(ENCLK) );
  
endmodule
