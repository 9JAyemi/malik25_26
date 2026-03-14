module BinaryCounter (count, clk, reset);

	output reg [3:0] count;
	input clk, reset;
	
	always @(posedge clk) begin
		if (reset) begin
			count <= 4'b0000;		// Reset count value to 0
		end
		else begin
			count <= count + 1;		// Increment count value by 1
		end
	end

endmodule