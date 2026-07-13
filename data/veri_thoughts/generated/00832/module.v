module TLATNTSCAX2TS_latch_module (CLK, EN, TE, ENCLK);
  input CLK, EN, TE;
  output ENCLK;
  
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