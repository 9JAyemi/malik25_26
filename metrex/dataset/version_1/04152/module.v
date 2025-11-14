module mag_comparator #(
  parameter n = 4 // number of bits in the binary numbers
)(
  input [n-1:0] A,
  input [n-1:0] B,
  output GT,
  output EQ,
  output LT
);


assign GT = (A > B);
assign EQ = (A == B);
assign LT = (A < B);

endmodule