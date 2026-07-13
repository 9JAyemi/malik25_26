module mux2x1 (a, b, s, y);
  input a, b, s;
  output y;

  assign y = (!s & a) | (s & b);
endmodule

module mux4x1 (a, b, c, d, sel0, sel1, y);
  input a, b, c, d, sel0, sel1;
  output y;

  wire w1, w2;

  mux2x1 m1(a, b, sel0, w1);
  mux2x1 m2(c, d, sel0, w2);
  mux2x1 m3(w1, w2, sel1, y);
endmodule