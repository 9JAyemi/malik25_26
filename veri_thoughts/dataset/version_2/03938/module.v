


module FrequencyDivider(clk,clk_out);

input clk;
    output reg clk_out;
    reg rst;
	 

	
	parameter Ts = 80;
	parameter Te = 20;
	parameter n = ((Ts/(2*Te))-1);	 
	 parameter bitCount = 31;
	 reg [bitCount:0] counter;initial
rst=0;always @(posedge clk or negedge rst)begin
      if(!rst)begin
       rst<=1;
       counter<=32'd0;
       clk_out <= 1'b0;end
		 
		 
		 else 
	 if(counter==n) 
         begin
         counter<=32'd0;
         clk_out <= ~clk_out;
         end
      else
       begin
       counter<=counter+1;
       end
   end
   
	


endmodule
