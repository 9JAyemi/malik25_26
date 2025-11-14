
module selem (
  input sreq_0n,
  input sreq_1n,
  output activateOut_0r,
  output activateOut_0a
);

  assign activateOut_0r = sreq_0n & sreq_1n;
  assign activateOut_0a = sreq_0n | sreq_1n;

endmodule
