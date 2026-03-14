module counter4(clk, enable, reset, out);

	output reg [3:0] out;
	input clk, enable, reset;
	
	always@(posedge clk or posedge reset) begin
		if(reset == 1'b1) begin
			out <= 4'b0;
		end
		else if(enable == 1'b1) begin
			out <= out + 1;
		end
	end
	
endmodule