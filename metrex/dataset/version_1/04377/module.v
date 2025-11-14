

module descrambler # (
	parameter WIDTH = 512
)(
	input clk,arst,ena,
	input [WIDTH-1:0] din,		output reg [WIDTH-1:0] dout
);

reg [57:0] scram_state;
wire [WIDTH+58-1:0] history;
wire [WIDTH-1:0] dout_w;
assign history = {din,scram_state};

genvar i;
generate
	for (i=0; i<WIDTH; i=i+1) begin : lp
		assign dout_w[i] = history[58+i-58] ^ history[58+i-39] ^ history[58+i];		
	end
endgenerate
	
always @(posedge clk or posedge arst) begin
	if (arst) begin
		dout <= 0;
		scram_state <= 58'h3ff_ffff_ffff_ffff;
	end
	else if (ena) begin
		dout <= dout_w;
		scram_state <= history[WIDTH+58-1:WIDTH];
	end
end

endmodule
	
