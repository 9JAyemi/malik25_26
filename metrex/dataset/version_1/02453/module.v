module ballcollisions(
	clk,
	reset,
	p1_y,
	p2_y,
	ball_x,
	ball_y,
	dir_x,
	dir_y,
	oob
);

input clk, reset;
input [10:0] p1_y, p2_y, ball_x, ball_y;
output reg dir_x, dir_y, oob;

// Constants
localparam hc = 512;
localparam va = 0;
localparam vc = 480;
localparam batwidth = 10;
localparam batheight = 80;
localparam ballsize = 10;

// Initial values
reg ball_x_reg, ball_y_reg;
reg dir_x_reg, dir_y_reg;
reg oob_reg;
initial begin
	ball_x_reg = hc;
	ball_y_reg = vc/2;
	dir_x_reg = 0;
	dir_y_reg = 1;
	oob_reg = 0;
end

// Logic for direction changes
always @ (posedge clk) begin
	if (reset) begin
		dir_x_reg <= ~dir_x_reg;
		dir_y_reg <= 1;
		oob_reg <= 0;
		ball_x_reg <= hc;
		ball_y_reg <= vc/2;
	end
	else begin
		// out of bounds (i.e. one of the players missed the ball)
		if (ball_x_reg <= 0 || ball_x_reg >= hc) begin
			oob_reg <= 1;
		end
		else begin
			oob_reg <= 0;
		end
		
		// collision with top & bottom walls
		if (ball_y_reg <= va + ballsize) begin
			dir_y_reg <= 1;
		end
		if (ball_y_reg >= vc - ballsize) begin
			dir_y_reg <= 0;
		end
		
		// collision with P1 bat
		if (ball_x_reg <= batwidth && ball_y_reg + ballsize >= p1_y && ball_y_reg <= p1_y + batheight) begin
			dir_x_reg <= 1;
			if (ball_y_reg + ballsize <= p1_y + (batheight / 2)) begin
				dir_y_reg <= 0;
			end
			else begin
				dir_y_reg <= 1;
			end
		end
		// collision with P2 bat
		else if (ball_x_reg >= hc - batwidth - ballsize && ball_y_reg + ballsize <= p2_y + batheight && ball_y_reg >= p2_y) begin
			dir_x_reg <= 0;
			if (ball_y_reg + ballsize <= p2_y + (batheight / 2)) begin
				dir_y_reg <= 0;
			end
			else begin
				dir_y_reg <= 1;
			end
		end
		
		// Move ball based on direction
		if (dir_x_reg) begin
			ball_x_reg <= ball_x_reg + 1;
		end
		else begin
			ball_x_reg <= ball_x_reg - 1;
		end
		
		if (dir_y_reg) begin
			ball_y_reg <= ball_y_reg + 1;
		end
		else begin
			ball_y_reg <= ball_y_reg - 1;
		end
	end
end

// Assign output signals to registered values
always @* begin
	dir_x = dir_x_reg;
	dir_y = dir_y_reg;
	oob = oob_reg;
end

endmodule