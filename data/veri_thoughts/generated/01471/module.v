
module clock_mux (
  input [n-1:0] clk,
  input sel,
  output clk_out
);

parameter n = 4; // number of input clock signals

reg clk_out_reg; // declare clk_out as a register

assign clk_out = clk_out_reg;

always @ (posedge clk[sel]) begin
  clk_out_reg <= clk[sel];
end

endmodule
