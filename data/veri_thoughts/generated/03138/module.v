
module dffl_2 ( clk, ld, d, reset, q );
	// synthesis attribute keep_hierarchy dffl_2 "true";
	input clk;
	input d;
	input ld;
	input reset;
	output q;
	reg q;
	always @(posedge clk) begin
	// leda XV2P_1006 off Multiple synchronous resets detected
	// leda XV2P_1007 off Multiple synchronous resets detected
	// leda G_551_1_K off Multiple synchronous resets detected
	if (reset) begin
		q <= 1'b0;
	end
	else if (ld)
		q <= d;
	// leda XV2P_1006 on Multiple synchronous resets detected
	// leda XV2P_1007 on Multiple synchronous resets detected
	// leda G_551_1_K on Multiple synchronous resets detected
	end
endmodule