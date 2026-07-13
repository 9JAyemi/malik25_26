
module ripple_carry_adder (
	input [3:0] A,
	input [3:0] B,
	input C_in,
	input clk,
	output [3:0] S,
	output C_out
);

	reg [3:0] S_reg;
	reg C_out_reg;

	always @(posedge clk) begin
		// calculate the sum of A, B, and C_in
		S_reg = A + B + C_in;

		// calculate the carry-out bit
		C_out_reg = ((A[3] & B[3]) | (A[3] & C_in) | (B[3] & C_in));
	end

	// assign outputs
	assign S = S_reg;
	assign C_out = C_out_reg;

endmodule
