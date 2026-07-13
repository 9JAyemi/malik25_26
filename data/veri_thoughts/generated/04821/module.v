module flop_sync_rst(
   input clk,
   input rst,
   input din,
   output reg q
);

always@(posedge clk)
   if(rst)
      q <= 0;
   else
      q <= din;

endmodule
