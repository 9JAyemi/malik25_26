module rsdec_syn_m0 (scale, y);
	input [8:0] y;
	output [8:0] scale;

	assign scale = 9'h1;
endmodule

module rsdec_syn_m1 (scale, y);
	input [8:0] y;
	output [8:0] scale;

	assign scale = 9'h2;
endmodule

module rsdec_syn_m2 (scale, y);
	input [8:0] y;
	output [8:0] scale;

	assign scale = 9'h4;
endmodule

module rsdec_syn_m3 (scale, y);
	input [8:0] y;
	output [8:0] scale;

	assign scale = 9'h8;
endmodule

module rsdec_syn_m4 (scale, y);
	input [8:0] y;
	output [8:0] scale;

	assign scale = 9'h10;
endmodule

module rsdec_syn_m5 (scale, y);
	input [8:0] y;
	output [8:0] scale;

	assign scale = 9'h20;
endmodule

module rsdec_syn_m6 (scale, y);
	input [8:0] y;
	output [8:0] scale;

	assign scale = 9'h40;
endmodule

module rsdec_syn_m7 (scale, y);
	input [8:0] y;
	output [8:0] scale;

	assign scale = 9'h80;
endmodule

module rsdec_syn (y0, y1, y2, y3, y4, y5, y6, y7, u, enable, shift, init, clk, clrn);
	input [8:0] u;
	input clk, clrn, shift, init, enable;
	output [8:0] y0;
	output [8:0] y1;
	output [8:0] y2;
	output [8:0] y3;
	output [8:0] y4;
	output [8:0] y5;
	output [8:0] y6;
	output [8:0] y7;
	reg [8:0] y0;
	reg [8:0] y1;
	reg [8:0] y2;
	reg [8:0] y3;
	reg [8:0] y4;
	reg [8:0] y5;
	reg [8:0] y6;
	reg [8:0] y7;

	wire [8:0] scale0;
	wire [8:0] scale1;
	wire [8:0] scale2;
	wire [8:0] scale3;
	wire [8:0] scale4;
	wire [8:0] scale5;
	wire [8:0] scale6;
	wire [8:0] scale7;

	rsdec_syn_m0 m0 (scale0, y0);
	rsdec_syn_m1 m1 (scale1, y1);
	rsdec_syn_m2 m2 (scale2, y2);
	rsdec_syn_m3 m3 (scale3, y3);
	rsdec_syn_m4 m4 (scale4, y4);
	rsdec_syn_m5 m5 (scale5, y5);
	rsdec_syn_m6 m6 (scale6, y6);
	rsdec_syn_m7 m7 (scale7, y7);

	always @ (posedge clk)// or negedge clrn)
	begin
		if (~clrn)
		begin
			y0 <= 0;
			y1 <= 0;
			y2 <= 0;
			y3 <= 0;
			y4 <= 0;
			y5 <= 0;
			y6 <= 0;
			y7 <= 0;
		end
		else if (init)
		begin
			y0 <= u;
			y1 <= u;
			y2 <= u;
			y3 <= u;
			y4 <= u;
			y5 <= u;
			y6 <= u;
			y7 <= u;
		end
		else if (enable)
		begin
			y0 <= scale0 ^ u;
			y1 <= scale1 ^ u;
			y2 <= scale2 ^ u;
			y3 <= scale3 ^ u;
			y4 <= scale4 ^ u;
			y5 <= scale5 ^ u;
			y6 <= scale6 ^ u;
			y7 <= scale7 ^ u;
		end
		else if (shift)
		begin
			y0 <= y1;
			y1 <= y2;
			y2 <= y3;
			y3 <= y4;
			y4 <= y5;
			y5 <= y6;
			y6 <= y7;
			y7 <= y0;
		end
	end

endmodule