module clock_gate (
  input CLK,
  input EN,
  input TE,
  output wire ECK
);

  TLATNTSCAX2TS latch (
    .E(EN),
    .SE(TE),
    .CK(CLK),
    .ECK(ECK)
  );


endmodule

module TLATNTSCAX2TS (
  input E,
  input SE,
  input CK,
  output reg ECK
);

  always @* begin
    ECK <= E & SE & CK;
  end

endmodule