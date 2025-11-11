
module sync_gray (
	input in_clk,
	input in_resetn,
	input [DATA_WIDTH-1:0] in_count,
	input out_resetn,
	input out_clk,
	output [DATA_WIDTH-1:0] out_count
);

parameter DATA_WIDTH = 1;
parameter CLK_ASYNC = 1;

reg [DATA_WIDTH-1:0] in_count_gray = 'h0;
reg [DATA_WIDTH-1:0] out_count_gray_m1 = 'h0;
reg [DATA_WIDTH-1:0] out_count_gray_m2 = 'h0;
reg [DATA_WIDTH-1:0] out_count_m = 'h0;

function [DATA_WIDTH-1:0] g2b;
	input [DATA_WIDTH-1:0] g;
	reg   [DATA_WIDTH-1:0] b;
	integer i;
	begin
		b[DATA_WIDTH-1] = g[DATA_WIDTH-1];
		for (i = DATA_WIDTH - 2; i >= 0; i =  i - 1)
			b[i] = b[i + 1] ^ g[i];
		g2b = b;
	end
endfunction

function [DATA_WIDTH-1:0] b2g;
	input [DATA_WIDTH-1:0] b;
	reg [DATA_WIDTH-1:0] g;
	integer i;
	begin
		g[DATA_WIDTH-1] = b[DATA_WIDTH-1];
		for (i = DATA_WIDTH - 2; i >= 0; i = i -1)
				g[i] = b[i + 1] ^ b[i];
		b2g = g;
	end
endfunction

always @(posedge in_clk) begin
	if (in_resetn == 1'b0) begin
		in_count_gray <= 'h00;
	end else begin
		in_count_gray <= b2g(in_count);
	end
end

always @(posedge out_clk) begin
	if (out_resetn == 1'b0) begin
		out_count_gray_m1 <= 'h00;
		out_count_gray_m2 <= 'h00;
		out_count_m <= 'h00;
	end else begin
		out_count_gray_m1 <= in_count_gray;
		out_count_gray_m2 <= out_count_gray_m1;
		out_count_m <= g2b(out_count_gray_m2);
	end
end

assign out_count = CLK_ASYNC ? out_count_m : in_count;

endmodule
