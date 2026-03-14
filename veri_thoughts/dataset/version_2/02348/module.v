
module SNPS_CLOCK_GATE_HIGH_RegisterAdd_W32_0_5 (input CLK, EN, TE, output ENCLK);
  TLATNTSCAX2TS latch (.E(EN), .SE(TE), .CK(CLK), .ECK(ENCLK));
endmodule
module TLATNTSCAX2TS (
    input E,
    input SE,
    input CK,
    output reg ECK
);
  always @(posedge CK) begin
    if (SE) begin
      ECK <= E;
    end
  end
endmodule