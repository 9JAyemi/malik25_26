module init(input wire clk, output ini);

reg ini = 0;
  
always @(posedge(clk))
  ini <= 1;

endmodule



