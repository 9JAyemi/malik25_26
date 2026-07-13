module AOI_OR(Z, A, B);
  input A, B;
  output Z;
  wire W1, W2, W3;
  aoi2x1 G1 (W1, A, B);
  aoi2x1 G2 (W2, A, W1);
  aoi2x1 G3 (W3, B, W1);
  aoi2x1 G4 (Z, W2, W3);
endmodule

module aoi2x1(Y, A, B);
  input A, B;
  output Y;
  assign Y = ~(A & B);
endmodule