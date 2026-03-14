
module counter(
	input wire clk,
	output reg [15:0] count
);

always @(posedge clk) begin
	if(count == 16'hFFFF) begin
		count <= 16'h0000;
	end
	else begin
		count <= count + 1'b1;
	end
end

endmodule