module full_adder (sum, carry_out, a, b, carry_in);
	output sum, carry_out;
	input a, b, carry_in;
	
	assign sum = a ^ b ^ carry_in;
	assign carry_out = (a & b) | (a & carry_in) | (b & carry_in);
endmodule

module four_bit_adder (A, B, C);
	input [3:0] A, B;
	output [4:0] C;
	
	wire [3:0] sum;
	wire [4:0] carry;
	
	full_adder fa0 (sum[0], carry[1], A[0], B[0], 1'b0);
	full_adder fa1 (sum[1], carry[2], A[1], B[1], carry[1]);
	full_adder fa2 (sum[2], carry[3], A[2], B[2], carry[2]);
	full_adder fa3 (sum[3], carry[4], A[3], B[3], carry[3]);
	
	assign C[0] = sum[0];
	assign C[1] = sum[1];
	assign C[2] = sum[2];
	assign C[3] = sum[3];
	assign C[4] = carry[4];
endmodule