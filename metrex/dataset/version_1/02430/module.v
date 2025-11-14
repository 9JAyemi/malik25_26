module SNPS_CLOCK_GATE_HIGH_RegisterAdd_W32_0_7 ( CLK, EN, ENCLK, TE );
  input CLK, EN, TE;
  output ENCLK;

  wire E, SE, CK, ECK;

  assign E = TE;
  assign SE = EN;
  assign CK = CLK;
  assign ENCLK = EN ? ECK : 1'b0;

  TLATNTSCAX2TS latch ( .E(E), .SE(SE), .CK(CK), .ECK(ECK) );

endmodule

module TLATNTSCAX2TS ( E, SE, CK, ECK );
  input E, SE, CK;
  output reg ECK;

  always @(posedge CK) begin
    if (SE) ECK <= E;
  end
endmodule