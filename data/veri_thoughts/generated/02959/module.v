module sync_reset_DFF (
	input D, GSR, CLK,
	output reg Q
);

	always @(posedge CLK) begin
		if (GSR) begin
			Q <= 1'b0;
		end else begin
			Q <= D;
		end
	end

endmodule