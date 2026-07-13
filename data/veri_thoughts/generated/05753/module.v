
module Comparator_Equal

# (parameter S = 1) 
	(
	input wire [S-1:0] Data_A,
	input wire [S-1:0] Data_B,
	output wire equal_sgn
    );

assign equal_sgn = (Data_A == Data_B) ? 1'b1 : 1'b0;
endmodule
