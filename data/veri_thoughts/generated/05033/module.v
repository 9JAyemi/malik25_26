module por (
	input			clk,
	output	reg		rst
);

reg	[31:0]	counter;

always @(posedge clk) begin
	if (counter < 32'hffffff) begin
		rst <= 1;
		counter <= counter + 1;
	end
	else begin
		rst <= 0;
	end
end

endmodule
