module nand4 (
  Y,
  A,
  B,
  C,
  D
);

  output Y;
  input A;
  input B;
  input C;
  input D;


  assign Y = ~( A & B & C & D);

endmodule