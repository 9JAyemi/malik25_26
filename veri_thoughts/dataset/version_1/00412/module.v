
module full_adder (
  input A, B, Ci,
  output S, Co
);

  wire w1, w2, w3;

  xor U1 (w1, A, B);
  xor U2 (S, w1, Ci);
  and U3 (w2, A, B);
  and U4 (w3, w1, Ci);
  or U5 (Co, w2, w3);

endmodule