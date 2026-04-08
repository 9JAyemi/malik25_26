module binary_counter #(parameter COUNTER_WIDTH=8)
	(
		input wire clk,
		input wire rst,
		output reg [COUNTER_WIDTH-1:0] count
	);

	always @(posedge clk) begin
		if (rst) begin
			count <= 0;
		end else begin
			count <= count + 1;
		end
	end

endmodule