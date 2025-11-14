

module debounce(input clk, but, output reg debounced);
	reg [9:0] debTimer;
	always @(posedge clk) begin
		if (debounced == but)
			debTimer <= 0;
		else if (debTimer != -10'b1)
			debTimer <= debTimer+1;
		else if (debTimer == -10'b1)
			debounced <= but;
	end
endmodule

module clkDiv(input clk, output divClk);
	parameter n = 25;
	reg [n-1:0] count = 0;
	assign divClk = count[n-1];
	
	always @(posedge clk)
		count <= count + 1;
endmodule
