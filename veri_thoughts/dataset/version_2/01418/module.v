
module clock_gate_d_ff_en(input CLK, EN, TE, output ENCLK);
  wire gated_clk;
  
  assign gated_clk = EN ? CLK : 1'b0;
  assign ENCLK = gated_clk;
  
endmodule