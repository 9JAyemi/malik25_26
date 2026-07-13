
module half_adder(
  input A,
  input B,
  output S,
  output C
);

  wire A_not = ~A;
  wire B_not = ~B;

  assign S = A_not & B | A & B_not;
  assign C = A & B;

endmodule