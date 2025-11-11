
module TLATNTSCAX2TS (
  input E,
  input SE,
  input CK,
  output ECK
);

  assign ECK = E & SE;

endmodule
module clock_gate (
  input CLK,
  input EN,
  input TE,
  output ENCLK
);
 
  assign ENCLK = EN & TE;

endmodule