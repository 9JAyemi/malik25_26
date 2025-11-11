module full_adder (A, B, Ci, S, Co);
  input A, B, Ci;
  output S, Co;
  wire n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11;

  assign n11 = ~(A ^ B);
  assign S = ~(Ci ^ n11);
  assign n10 = ~(A & B & Ci);
  assign n9 = ~(A & B);
  assign Co = ~(n10 & n9);
  assign n1 = ~(Ci & n11);
  assign n2 = ~(B & n11);
  assign n3 = ~(A & Ci);
  assign n4 = ~(n1 & n2);
  assign n5 = ~(n3 & n9);
  assign n6 = ~(n3 & n2);
  assign n7 = ~(n1 & n9);
  assign n8 = ~(n6 & n7);
endmodule