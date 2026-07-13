module FA_106 (input A, B, Ci, output S, Co);
  wire n9, n10, n11;

  assign n11 = ~(A ^ B);
  assign S = ~(Ci ^ n11);
  assign n10 = ~(A & B & Ci);
  assign n9 = ~(A & B);
  assign Co = ~(n10 & n9);
endmodule