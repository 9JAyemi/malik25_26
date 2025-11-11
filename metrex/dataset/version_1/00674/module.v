
module TLATNTSCAX2TS (E, SE, CK, ECK);
  input E, SE, CK;
  output ECK;

  assign ECK = E & SE;

endmodule
