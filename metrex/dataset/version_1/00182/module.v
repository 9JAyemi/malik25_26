module delay_800ns(input clk, input reset, input in, output reg p);
	reg [31:0] count;
	always @(posedge clk or posedge reset) begin
		if(reset) begin
			count <= 0;
			p <= 0;
		end
		else begin
			if(in && !p) begin
				count <= 0;
				p <= 1;
			end
			else if(count < 200) begin
				count <= count + 1;
			end
			else begin
				count <= 0;
				p <= 0;
			end
		end
	end
endmodule