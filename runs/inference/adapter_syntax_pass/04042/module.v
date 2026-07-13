module clock_gate (
  input CLK,
  input EN,
  input TE,
  output ENCLK
);

  TLATNTSCAX2TS latch ( .E(EN), .SE(TE), .CK(CLK), .ECK(ENCLK) );

endmodule

module TLATNTSCAX2TS (
  input E,
  input SE,
  input CK,
  output reg ECK
);

  always @ (posedge CK) begin
    if (SE)
      ECK <= E;
  end

endmodule