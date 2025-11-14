
module SNPS_CLOCK_GATE_HIGH_RegisterAdd_W55_0_2 (input CLK, EN, TE, output ENCLK);
  assign ENCLK = EN ? CLK : 1'b0;

  TLATNTSCAX2TS latch ( .E(EN), .SE(TE), .CK(CLK), .ECK(ENCLK) );

endmodule
module TLATNTSCAX2TS (input E, SE, CK, ECK);
  // Add your TLATNTSCAX2TS module implementation here
endmodule