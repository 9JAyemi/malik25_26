module clock_gate_high (
  input CLK,
  input EN,
  input TE,
  output ENCLK
);

  wire n2;
  TLATNTSCAX2TS latch (
    .E(EN),
    .SE(TE),
    .CK(CLK),
    .ECK(n2)
  );
  BUFX6TS buffer (
    .I(n2),
    .O(ENCLK)
  );

endmodule

module TLATNTSCAX2TS (
  input E,
  input SE,
  input CK,
  output reg ECK
);

always @ (posedge CK or posedge SE)
  if (SE)
    ECK <= 1'b0;
  else
    ECK <= E;

endmodule

module BUFX6TS (
  input I,
  output O
);

assign O = I;

endmodule