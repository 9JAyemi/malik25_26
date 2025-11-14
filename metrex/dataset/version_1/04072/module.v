module clock_multiplexer (
  input [3:0] clk,
  input [1:0] control,
  output reg clk_out
);

parameter n = 4; // number of input clock signals

always @ (posedge clk[control])
  clk_out <= clk[control];

endmodule