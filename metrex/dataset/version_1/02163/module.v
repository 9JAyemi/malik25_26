module full_adder ( input A, B, Ci, output S, Co );
  wire   n1, n2, n3;

  assign n1 = ~(A ^ B);
  assign n2 = ~(n1 ^ Ci);
  assign n3 = ~(A ^ Ci);
  assign Co = n1 & Ci;
  assign S = n2 & n3;

endmodule