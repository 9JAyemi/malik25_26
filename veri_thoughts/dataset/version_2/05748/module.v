module GrayCodeConverter (
  input [n-1:0] bin,
  output [n-1:0] gray
);

parameter n = 4; // number of bits in the binary number and Gray code

assign gray = bin ^ ({1'b0, bin}) >> 1;

endmodule