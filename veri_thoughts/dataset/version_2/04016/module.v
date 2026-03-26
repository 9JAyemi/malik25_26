module CLKSKW(
	input CLKI,
	input [3:0] SKW,
	input RST,
	output reg CLKO
);

	reg [3:0] delay_reg;

	always @(posedge CLKI or posedge RST) begin
		if (RST) begin
			CLKO <= 1'b0;
			delay_reg <= 4'b0;
		end
		else begin
			delay_reg <= {delay_reg[2:0], CLKI};
			if (SKW[3]) begin
				CLKO <= delay_reg[SKW[2:0]] & ~delay_reg[SKW[2:0]-1];
			end
			else begin
				CLKO <= delay_reg[SKW[2:0]] & ~delay_reg[SKW[2:0]+1];
			end
		end
	end

endmodule