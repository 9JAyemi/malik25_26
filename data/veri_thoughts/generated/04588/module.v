module slice_module(Din, Dout);
  input [17:0] Din;
  output [7:0] Dout;
  wire [7:0] slice;

  assign slice = Din[Din[7:0] + 8];  // Corrected syntax for array indexing
  assign Dout = slice;
endmodule