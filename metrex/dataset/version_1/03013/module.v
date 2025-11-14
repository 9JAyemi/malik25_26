
module sevenseg
(
	input wire        clk,
	input wire        rstn,
	input wire  [7:0] display_0,
	input wire  [7:0] display_1,
	input wire  [7:0] display_2,
	input wire  [7:0] display_3,
	input wire  [1:0] decplace,
	output reg  [7:0] seg,
	output reg  [3:0] an
);

localparam NUM_0     = 8'b11000000;
localparam NUM_1     = 8'b11111001;
localparam NUM_2     = 8'b10100100;
localparam NUM_3     = 8'b10110000;
localparam NUM_4     = 8'b10011001;
localparam NUM_5     = 8'b10010010;
localparam NUM_6     = 8'b10000010;
localparam NUM_7     = 8'b11111000;
localparam NUM_8     = 8'b10000000;
localparam NUM_9     = 8'b10010000;
localparam CHAR_A    = 8'b10001000;
localparam CHAR_B    = 8'b10000011;
localparam CHAR_C    = 8'b11000110;
localparam CHAR_D    = 8'b10100001;
localparam CHAR_E    = 8'b10000110;
localparam CHAR_F    = 8'b10001110;
localparam CHAR_G    = 8'b10000010; localparam CHAR_H    = 8'b10001001;
localparam CHAR_K    = 8'b10001111;
localparam CHAR_L    = 8'b11000111;
localparam CHAR_o    = 8'b10100011;
localparam CHAR_S    = 8'b10010010; localparam CHAR_T    = 8'b11111000; localparam CHAR_P    = 8'b10001100;
localparam SPACE     = 8'b11111111;
localparam HYPHEN    = 8'b10111111;
localparam UNDERLINE = 8'b11110111;
localparam OVERRLINE = 8'b11111110;


reg  [16:0] cnt;
reg  [7:0]  digit;

always @(cnt[16:15]) begin
	case (cnt[16:15])
		2'b11:   an <= 4'b1110;
		2'b10:   an <= 4'b1101;
		2'b01:   an <= 4'b1011;
		default: an <= 4'b0111;
	endcase
end

always @(cnt[16:15] or display_0 or display_1 or display_2 or display_3) begin
	case (cnt[16:15])
		2'b00:   digit <= display_0;
		2'b01:   digit <= display_1;
		2'b10:   digit <= display_2;
		default: digit <= display_3;
	endcase

	case (digit)
		8'h20: seg <= SPACE;
		8'h2d: seg <= HYPHEN;
		8'h30: seg <= NUM_0;
		8'h31: seg <= NUM_1;
		8'h32: seg <= NUM_2;
		8'h33: seg <= NUM_3;
		8'h34: seg <= NUM_4;
		8'h35: seg <= NUM_5;
		8'h36: seg <= NUM_6;
		8'h37: seg <= NUM_7;
		8'h38: seg <= NUM_8;
		8'h39: seg <= NUM_9;
		8'h41: seg <= CHAR_A;
		8'h43: seg <= CHAR_C;
		8'h45: seg <= CHAR_E;
		8'h47: seg <= CHAR_G;
		8'h48: seg <= CHAR_H;
		8'h4b: seg <= CHAR_K;
		8'h4c: seg <= CHAR_L;
		8'h50: seg <= CHAR_P;
		8'h53: seg <= CHAR_S;
		8'h5f: seg <= UNDERLINE;
		8'h6f: seg <= CHAR_o;
		default: seg <= OVERRLINE;
	endcase
end

always @(posedge clk or negedge rstn) begin
	if (!rstn) begin
		cnt <= 0;
	end
	else
		cnt <= cnt + 1;
end

endmodule
