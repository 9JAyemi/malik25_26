module delay_1ms(input clk, input reset, input in, output out);
	reg [19:0] r;
	always @(posedge clk or posedge reset) begin
		if(reset)
			r <= 0;
		else begin
			if(in)
				r <= r + 20'b1;
			else
				r <= 0;
		end
	end
	assign out = r >= 1000;
endmodule