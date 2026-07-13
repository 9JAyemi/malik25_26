module dffsi_4 ( clk, reset, init, d, q );
	input clk;
	input reset;
	input [3:0] init;
	input [3:0] d;
	output [3:0] q;
	reg [3:0] q;

	always @(posedge clk) begin
	if (reset)
	q <= init;
	else
	q <= d;
	end
endmodule