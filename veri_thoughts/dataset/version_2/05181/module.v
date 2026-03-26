
module Coun_Baud#(parameter N=10, M=656)(  input wire clk, reset,
	output wire max_tick
	);
	
	reg [N-1:0] r_reg=0;
	wire [N-1:0] r_next;

	always @ (posedge clk , posedge reset)
		if (reset)
			r_reg <= 0 ;
		else
			r_reg <= r_next;
			
	assign r_next = (r_reg==(M-1)) ? 0 : r_reg + 1;
	
	assign max_tick = (r_reg==(M-1)) ? 1'b1 : 1'b0;

endmodule
