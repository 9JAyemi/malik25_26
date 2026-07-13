module gray_converter #(
  parameter n = 4
)(
  input [n-1:0] binary_in,
  output [n-1:0] gray_out
);


assign gray_out[0] = binary_in[0];

generate
  genvar i;
  for (i = 1; i < n; i = i + 1) begin : gray_gen
    assign gray_out[i] = binary_in[i] ^ gray_out[i-1];
  end
endgenerate

endmodule