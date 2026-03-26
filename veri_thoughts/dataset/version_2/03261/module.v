

module clk_div(
	input clk,
	input wire rst,
	input wire SW2,
	output reg[31:0] clkdiv,
	output wire Clk_CPU
    );


always @(posedge clk or posedge rst)begin
	if (rst) begin
		clkdiv <= 0;
	end else begin
		clkdiv <= clkdiv + 1'b1;
	end
end

assign Clk_CPU = clk;

endmodule
