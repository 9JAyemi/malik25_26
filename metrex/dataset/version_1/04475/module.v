module vga_renderer
	#(parameter WIDTH = 800,          H_FRONT_PORCH = 32,   H_SYNC = 120,          H_BACK_PORCH = 32,    HEIGHT = 480,         V_FRONT_PORCH = 8,   V_SYNC = 5,           V_BACK_PORCH = 13)    (
	 input vga_clk,
	 
	 input reset_n,
	 
	 input [7:0] red,
	 input [7:0] green,
	 input [7:0] blue,
	 
	 output [7:0] vga_red,
	 output [7:0] vga_green,
	 output [7:0] vga_blue,
	 
	 output vga_hsync,
	 output vga_vsync,
	 
	 output fb_hblank,
	 output fb_vblank
	);
	
	localparam PIXELS_PER_LINE = WIDTH + H_BACK_PORCH + H_SYNC + H_FRONT_PORCH;
	localparam LINES_PER_FRAME = HEIGHT + V_BACK_PORCH + V_SYNC + V_FRONT_PORCH;
	
	localparam XBITS = $clog2(PIXELS_PER_LINE);
	localparam YBITS = $clog2(LINES_PER_FRAME);
	
	reg [XBITS-1:0] x_pos;
	wire x_max = (x_pos == (PIXELS_PER_LINE - 1));
	
	reg [YBITS-1:0] y_pos;
	wire y_max = (y_pos == (LINES_PER_FRAME - 1));
	
	reg hsync;
	assign vga_hsync = ~hsync;
	
	reg vsync;
	assign vga_vsync = ~vsync;
	
	assign fb_vblank = (y_pos >= HEIGHT);
	assign fb_hblank = (x_pos >= WIDTH);
	
	always @ (posedge vga_clk or negedge reset_n) begin
		if(~reset_n) begin
			x_pos <= 0;
			y_pos <= 0;
			hsync <= 1'b0;
			vsync <= 1'b0;
		end else begin
			if(x_max) begin
				x_pos <= 0;
				if(y_max) begin
					y_pos <= 0;
				end else begin
					y_pos <= y_pos + 1;
				end
			end else begin
				x_pos <= x_pos + 1;
			end
			
			if(x_pos == ((WIDTH + H_FRONT_PORCH) - 1)) hsync <= 1'b1;
			else if(x_pos == ((WIDTH + H_FRONT_PORCH + H_SYNC) - 1)) hsync <= 1'b0;
			
			if(y_pos == ((HEIGHT + V_FRONT_PORCH) - 1)) vsync <= 1'b1;
			else if(y_pos == ((HEIGHT + V_FRONT_PORCH + V_SYNC) - 1)) vsync <= 1'b0;
		end
	end

	assign vga_red = (x_pos < WIDTH && y_pos < HEIGHT) ? red : 8'b0;
	assign vga_green = (x_pos < WIDTH && y_pos < HEIGHT) ? green : 8'b0;
	assign vga_blue = (x_pos < WIDTH && y_pos < HEIGHT) ? blue : 8'b0;
	
endmodule
	 