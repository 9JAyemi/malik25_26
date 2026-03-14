module my_module(
  input A1,
  input A2,
  input B,
  output O
);

  wire w0;

  or(w0, A1, A2);

  nand(O, w0, B);

endmodule