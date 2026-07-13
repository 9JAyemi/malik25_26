module gray_converter #(
  parameter n = 4 // number of bits in the binary and gray code
) (
  input [n-1:0] bin,
  output [n-1:0] gray
);


assign gray[n-1] = bin[n-1];
genvar i;
generate
  for (i = 0; i < n-1; i=i+1) begin
    assign gray[i] = bin[i] ^ bin[i+1];
  end
endgenerate

endmodule
