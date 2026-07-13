module bin_to_gray(
    input [31:0] bin_in,
    output [31:0] gray_out
);

assign gray_out = bin_in ^ (bin_in >> 1);

endmodule

