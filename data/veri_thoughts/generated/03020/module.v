
module bin2gray(
    input [2:0] bin_in,
    output [2:0] gray_out
);

// Implement the gray code conversion using behavioral modeling
assign gray_out[2] = bin_in[2];
assign gray_out[1] = bin_in[2] ^ bin_in[1];
assign gray_out[0] = bin_in[1] ^ bin_in[0];

endmodule
