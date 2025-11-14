`define TOTAL_SCREEN_WIDTH 795
`define TOTAL_SCREEN_HEIGHT 525
`define VISIBLE_SCREEN_WIDTH 640
`define VISIBLE_SCREEN_HEIGHT 480

module VGA_DRIVER (
	RESET,
	CLOCK,
	PIXEL_COLOR_IN,
	PIXEL_X,
	PIXEL_Y,
	PIXEL_COLOR_OUT,
	H_SYNC_NEG,
	V_SYNC_NEG
);



input CLOCK; input RESET;
input  [7:0] PIXEL_COLOR_IN; output [9:0] PIXEL_X; output [9:0] PIXEL_Y; output [7:0] PIXEL_COLOR_OUT; output       H_SYNC_NEG; output       V_SYNC_NEG; 

reg  [9:0] pixel_count;
reg  [9:0] line_count;


assign PIXEL_X    = pixel_count;
assign PIXEL_Y    = line_count;

assign PIXEL_COLOR_OUT = (pixel_count<(`VISIBLE_SCREEN_WIDTH) )
									? (PIXEL_COLOR_IN) : (8'b00000000) ; assign H_SYNC_NEG = (pixel_count>=656 && pixel_count<752) ? (1'b0) : (1'b1); assign V_SYNC_NEG = (line_count>=490 && line_count<492) ? (1'b0) : (1'b1); always @(posedge CLOCK) begin
	if (RESET) begin
		pixel_count <= 10'b0;
		line_count <= 10'b0;
	end
	else if (pixel_count == (`TOTAL_SCREEN_WIDTH-1)) begin
		pixel_count <= 0;
		if (line_count == (`TOTAL_SCREEN_HEIGHT-1)) begin
		line_count <= 0;
		end 
		else begin
		line_count <= line_count + 1;
		end
	end 
	else begin
		pixel_count <= pixel_count + 1;
		line_count <= line_count;
	end
end

endmodule
