
module RGB_color_set(
	input clk,
	input [1:0] button,
	output [23:0] RGBcolor
    );

	reg [1:0] cunt = 2'd0;
	reg [7:0] red;
	reg [7:0] gre;
	reg [7:0] blu;

	always @ (posedge button[0])
		begin
			cunt <= cunt+1;
		end

	always @ (posedge clk)
		begin

		if(button[1]) begin
			red <= 8'b01011111;
			gre <= 8'b01011111;
			blu <= 8'b01011111;
		end

		else if (cunt == 1)begin
			red <= 8'b01111111;
			gre <= 8'b00000000;
			blu <= 8'b00000000;
			end

		else if (cunt == 2)begin
			red <= 8'b00000000;
			gre <= 8'b01111111;
			blu <= 8'b00000000;
			end

		else if (cunt == 3)begin
			red <= 8'b00000000;
			gre <= 8'b00000000;
			blu <= 8'b01111111;
			end

		else begin
			red <= 8'b00111111;
			gre <= 8'b00111111;
			blu <= 8'b00111111;
			end

		end

	assign RGBcolor = {red, gre, blu};

endmodule
