module DCSC(
	input CLK1, CLK0,
	input SEL1, SEL0,
	input MODESEL,
	output DCSOUT
);
	parameter DCSMODE = "POS";  // Default DCSMODE is "POS"

	reg DCS1, DCS0;   // Intermediate registers
	wire DCS_OR, DCS_XOR, DCS_AND;

	// Generate intermediate signals
	assign DCS_OR = CLK1 | CLK0;
	assign DCS_XOR = CLK1 ^ CLK0;
	assign DCS_AND = CLK1 & CLK0;

	// Generate DCSOUT based on MODESEL and SEL1/SEL0
	always @(*) begin
		if (MODESEL) begin
			DCS1 <= DCS_AND;
			DCS0 <= DCS_AND;
		end else begin
			if (SEL1 && !SEL0) begin
				DCS1 <= CLK1;
				DCS0 <= DCS_AND;
			end else if (!SEL1 && SEL0) begin
				DCS1 <= DCS_AND;
				DCS0 <= CLK0;
			end else if (SEL1 && SEL0) begin
				DCS1 <= DCS_OR;
				DCS0 <= DCS_AND;
			end else begin
				DCS1 <= DCS_XOR;
				DCS0 <= DCS_AND;
			end
		end
	end

	// Invert DCSOUT if DCSMODE is "NEG"
	assign DCSOUT = (DCSMODE == "NEG") ? (~DCS0) : (DCS1);  // Use DCS1 and DCS0 to generate the final DCSOUT

endmodule