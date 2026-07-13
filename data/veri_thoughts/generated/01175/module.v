
module and4 (
  input A,
  input B,
  input C,
  input D,
  output Y
);

  wire w1, w2;

  and (w1, A, B, C);
  and (w2, w1, D);
  assign Y = w2;

endmodule