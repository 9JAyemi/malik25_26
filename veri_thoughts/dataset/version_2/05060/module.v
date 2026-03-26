module onehot0(
  input  [31:0] in,
  output  out
);

  assign out = ((in & (in - 1)) == 0) && (in[0] == 0);

endmodule