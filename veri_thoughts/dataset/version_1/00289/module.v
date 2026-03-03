module AND_GATE(
	input D0, D1, RST, ECLK, SCLK,
	output Q
);
	parameter GSR = "ENABLED";
	
	reg Q_reg;

	always @(posedge SCLK) begin
		if (RST == (GSR == "ENABLED")) begin // Active-high reset
			Q_reg <= 1'b0;
		end else if (ECLK == 1'b1) begin
			Q_reg <= D0 & D1;
		end
	end

	assign Q = Q_reg;

endmodule