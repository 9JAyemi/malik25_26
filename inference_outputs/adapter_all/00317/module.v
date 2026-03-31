module TLATNTSCAX2TS (E, SE, CK, ECK);
  input E, SE, CK;
  output ECK;

  reg ECK;

  always @(posedge CK) begin
    if (SE) begin
      ECK <= E;
    end
  end
endmodule

module SNPS_CLOCK_GATE_HIGH_RegisterAdd_W32_1_1 (CLK, EN, ENCLK, TE);
  input CLK, EN, TE;
  output ENCLK;

  wire E, SE, CK, ECK;

  TLATNTSCAX2TS latch (.E(E), .SE(SE), .CK(CK), .ECK(ECK));

  assign E = EN;
  assign SE = TE;
  assign CK = CLK;
  assign ENCLK = ECK;

endmodule