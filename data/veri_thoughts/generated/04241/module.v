


module counter (count, clk, reset);
output [7:0] count;
input clk, reset;

reg [7:0] count;

always @ (posedge clk or posedge reset)
  if (reset)
     count = 8'h00;
  else
     count <= count + 8'h01;
     
endmodule



