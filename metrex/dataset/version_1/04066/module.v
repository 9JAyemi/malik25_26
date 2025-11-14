module signed_mult #(
	parameter A_WIDTH = 0,
	parameter B_WIDTH = 0,
	parameter P_WIDTH = 0
)(
	input signed [A_WIDTH-1:0] A,
	input signed [B_WIDTH-1:0] B,
	output reg signed [P_WIDTH-1:0] P
);

	always @(*)
	begin
		P <= A * B;
	end

endmodule