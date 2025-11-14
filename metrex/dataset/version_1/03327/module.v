
module single_module (T, C, E, Q);
	input T, C, E;
	output reg Q;

	wire xorout;

	assign xorout = T ^ Q;

	always @ (posedge C) begin
		if (E) begin
			Q = xorout;
		end
	end
endmodule