
module MUX2(
	input A, B, S, CLK, RST,
	output reg Y
);

	always @(posedge CLK or negedge RST) begin
		if(RST == 0) begin
			Y <= 0;
		end
		else begin
			if(S == 0) begin
				Y <= A;
			end
			else begin
				Y <= B;
			end
		end
	end

endmodule