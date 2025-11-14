module xlslice (
  input wire [23:0] Din,
  output wire [8:0] Dout
);

  wire [15:0] sliced_signal;
  wire [15:0] inverted_signal;
  wire [8:0] shifted_signal;

  assign sliced_signal = Din[22:7];
  assign inverted_signal = ~sliced_signal;
  assign shifted_signal = inverted_signal >> 8;

  assign Dout = shifted_signal;

endmodule