




module prog_counter2 (out_pc,rst,clk);

	output [0:31] out_pc;
	
	
	
	
	input clk;
	input rst;
	
	
	
	
	
	
	reg [0:31] out_pc;		always @(posedge clk)
	begin
		if(rst==1)
		begin
			out_pc<=32'd0;
		end
		else
		begin
			out_pc<=out_pc+32'd4;
		end
	end
	
	
	
	
endmodule
