
module stratixv_pll_dpa_output #(
	parameter output_clock_frequency = 0,	//Valid values: 
	parameter pll_vcoph_div = 1	//Valid values: 1|2|4
)(
	input [0:0] pd,
	input [7:0] phin,
	output [7:0] phout
);

	wire [7:0] input_clk_freq;
	assign input_clk_freq = phin + 40;

	wire [7:0] output_clk_freq;
	assign output_clk_freq = input_clk_freq * pll_vcoph_div;

	stratixv_pll_dpa_output_internal stratixv_pll_dpa_output_internal_inst (
		.pd(pd),
		.phin(phin),
		.phout(phout)
	);

endmodule
module stratixv_pll_dpa_output_internal #(
	parameter output_clock_frequency = 0,	//Valid values: 
	parameter pll_vcoph_div = 1	//Valid values: 1|2|4
)(
	input [0:0] pd,
	input [7:0] phin,
	output [7:0] phout
);


	wire [7:0] input_clk_freq;
	assign input_clk_freq = phin + 40;

	wire [7:0] output_clk_freq;
	assign output_clk_freq = input_clk_freq * pll_vcoph_div;
	assign phout = output_clk_freq;

endmodule