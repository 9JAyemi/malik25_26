module bidirectional_data_port (
  input clk,
  input reset,
  input [15:0] in,
  inout [15:0] out
);

  assign out = (in > 16'h7FFF) ? (~in + 16'h1) : in;
  
endmodule
