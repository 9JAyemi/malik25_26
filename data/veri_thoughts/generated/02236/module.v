module gray_code_converter (
  input [3:0] in,
  output [3:0] gray_out
);

  wire [3:0] gray_out;  // Declare gray_out as a wire type

  assign gray_out[0] = in[0];
  assign gray_out[1] = in[0] ^ in[1];
  assign gray_out[2] = in[1] ^ in[2];
  assign gray_out[3] = in[2] ^ in[3];

endmodule