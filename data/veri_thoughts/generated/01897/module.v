module full_adder(
  input A,
  input B,
  input C_in,
  output Sum,
  output C_out
);

  assign Sum = A ^ B ^ C_in;
  assign C_out = (A & B) | (C_in & (A ^ B));

endmodule