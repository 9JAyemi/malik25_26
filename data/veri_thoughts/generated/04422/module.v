module calculator (
  input [3:0] a,
  input [3:0] b,
  input op,
  output [3:0] result
);

  assign result = op ? a - b : a + b;

endmodule
