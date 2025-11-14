module counter(
	input clk,
	input rst,
	input en,
	input up_down,
	output reg [3:0] out
);

	always @(posedge clk or negedge rst) begin
		if (!rst) begin
			out <= 4'b0000;
		end else if (en) begin
			if (up_down) begin
				if (out == 4'b1111) begin
					out <= 4'b0000;
				end else begin
					out <= out + 1;
				end
			end else begin
				if (out == 4'b0000) begin
					out <= 4'b1111;
				end else begin
					out <= out - 1;
				end
			end
		end
	end

endmodule