
module TLATNTSCAX2TS (
  input E,
  input SE,
  input CK,
  output ECK
);

  assign ECK = E & SE ? CK : 1'b0;

endmodule
