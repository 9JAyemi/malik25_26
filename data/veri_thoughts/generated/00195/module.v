

module global_reset(
	input clock_i,
	input forced_reset_i,		output n_reset_o,				output n_limited_reset_o	);

	reg [7:0] reset_counter = 1;
	
	assign n_reset_o 				= (reset_counter <= 1) & !forced_reset_i;	
	assign n_limited_reset_o 	= (reset_counter <= 1);	
	always @(negedge clock_i)
		if( reset_counter != 0 )
			reset_counter <= reset_counter + 1'd1;
	
endmodule
