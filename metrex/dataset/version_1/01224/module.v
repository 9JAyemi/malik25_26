
module binary_to_gray(
  input [7:0] bin_in,
  output [7:0] gray_out
);

  wire [7:0] bin_to_gray; // Temporary variable to calculate binary code

  // Calculate binary code by xoring gray_out with shifted bin_to_gray
  assign gray_out = bin_in ^ ({bin_in[7], bin_in[7:1]});
  assign bin_to_gray = gray_out ^ ({gray_out[7], gray_out[7:1]});

endmodule