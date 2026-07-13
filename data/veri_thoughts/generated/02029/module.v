
module TLATNTSCAX2TS(E, SE, CK, ECK);

  input E, SE, CK;
  output ECK;

  assign ECK = SE ? CK : E ? 1'b1 : 1'b0;

endmodule

module register_clock_gate(CLK, EN, TE, ENCLK);

  input CLK;
  input EN;
  input TE;
  output ENCLK;

  TLATNTSCAX2TS latch (.E(EN), .SE(TE), .CK(CLK), .ECK(ENCLK));

endmodule
