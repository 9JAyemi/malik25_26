module GrayCodeConverter #(
  parameter n = 4 // number of bits
)(
  input [n-1:0] bin,
  input [n-1:0] gray,
  output [n-1:0] gray_out,
  output [n-1:0] bin_out
);


assign gray_out = bin ^ (bin >> 1);
assign bin_out = gray ^ (gray >> 1);

endmodule