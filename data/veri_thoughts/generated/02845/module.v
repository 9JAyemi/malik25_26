
module TLATNTSCAX2TS (E, SE, CK, D, ECK);
  input E, SE, CK, D;
  output ECK;

  assign ECK = (E & SE) ? D : CK;
endmodule

module SNPS_CLOCK_GATE_HIGH_RegisterAdd_W63_0_8 ( CLK, EN, TE, ADD_W63_0_8, ENCLK);
  input CLK, EN, TE;
  input [62:0] ADD_W63_0_8;
  output ENCLK;

  wire ECK;

  TLATNTSCAX2TS latch ( .E(EN), .SE(TE), .CK(CLK), .D(ADD_W63_0_8[0]), .ECK(ECK) );

  assign ENCLK = ECK;

endmodule
