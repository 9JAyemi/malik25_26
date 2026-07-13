
module clock_multiplexer_4 (
  input [3:0] clk,  // 4 clock signals
  input [1:0] ctrl, // 2-bit control signal
  output out_clk
);

parameter N = 4; // number of clock signals

assign out_clk = (ctrl < N) ? clk[ctrl] : 1'b0;

endmodule

module clock_multiplexer_8 (
  input [7:0] clk,  // 8 clock signals
  input [2:0] ctrl, // 3-bit control signal
  output out_clk
);

parameter N = 8; // number of clock signals

assign out_clk = (ctrl < N) ? clk[ctrl] : 1'b0;

endmodule
