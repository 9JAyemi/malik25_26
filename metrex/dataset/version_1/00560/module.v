module vga512x256 (
	input wire clk,
	input wire rst,
	output wire [12:0] maddr,	input wire [15:0] mdata,	output wire red,
	output wire green,
	output wire blue,
	output wire hsync,
	output wire vsync);

	parameter B = 50;	parameter C = 92;	parameter D = 512;	parameter E = 36;	parameter P = 4;	parameter Q = 61;	parameter R = 512;	parameter S = 31;	reg [9:0] cnt_x;
	reg [9:0] cnt_y;

	reg [15:0] word;

	assign red = word[0];
	assign green = word[0];
	assign blue = word[0];

	assign maddr = { cnt_y[8:1], cnt_x[8:4] };

	assign hsync = ~(cnt_x > (D + E) && cnt_x <= (D + E + B));
	assign vsync = ~(cnt_y >= (R + S) && cnt_y < (R + S + P));

	always @(posedge clk) begin
		if (rst || cnt_x == (B + C + D + E - 1))
			cnt_x <= 0;
		else
			cnt_x <= cnt_x + 1;

		if (rst)
			cnt_y <= 0;
		else if (cnt_x == (B + C + D + E - 1)) begin
			if (cnt_y == (P + Q + R + S - 1))
				cnt_y <= 0;
			else
				cnt_y <= cnt_y + 1;
		end

		if (cnt_x[3:0] == 1) begin
			if (cnt_x <= D && cnt_y < R)
				word <= mdata;
			else
				word <= 0;
		end else
			word <= { 1'b0, word[15:1] };
	end
endmodule
