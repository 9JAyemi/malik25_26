module dpram(wclk,wdata,waddr,wen,rclk,rdata,raddr);
   parameter depth = 4;
   parameter width = 16;
   parameter size = 16;
   
   input wclk;
   input [width-1:0] wdata;
   input [depth-1:0] waddr;
   input 	     wen;

   input rclk;
   output reg [width-1:0] rdata;
   input [depth-1:0]  raddr;
   
   reg [width-1:0]    ram [0:size-1];
   
   always @(posedge wclk)
     if(wen)
       ram[waddr] <= #1 wdata;
   
   always @(posedge rclk)
     rdata <= #1 ram[raddr];
   
endmodule 