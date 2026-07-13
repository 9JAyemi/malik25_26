


module Adder(din_a, din_b, din_c, dout);

	
	input wire[3:0] din_a;

	
	input wire[3:0] din_b;

	
	input wire[3:0] din_c;

	
	output wire[3:0] dout;

	

	assign dout = din_a + din_b;
	endmodule
