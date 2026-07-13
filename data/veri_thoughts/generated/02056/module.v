
module bin_to_gray(
    input [7:0] bin_in, // Assuming 8-bit input for demonstration purposes
    output [7:0] gray_out
);

    assign gray_out = bin_in ^ (bin_in >> 1);

endmodule
