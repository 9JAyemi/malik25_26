
module CLS_LED_Output_Multiplexer
(
	input [9:0]		PWM_CHANNEL_SIGS,
	input 			PWM_TIMER_TICK,
	input 			SRT_TICK,
	output reg [9:0] 	LEDR,
	input 			CLK
);
	
	reg [4:0] frame_pos;
	reg [4:0] next_frame_pos;
	reg [4:0] frame_pos_sync;
	wire [9:0] pchs = PWM_CHANNEL_SIGS;
	
	initial
	begin
		frame_pos = 5'h0;
		next_frame_pos = 5'h0;
	end

	always @(*)
	begin
		case (frame_pos)
			5'b00000 : next_frame_pos <= 5'b00001;
			5'b00001 : next_frame_pos <= 5'b00011;
			5'b00011 : next_frame_pos <= 5'b00010;
			5'b00010 : next_frame_pos <= 5'b00110;
			5'b00110 : next_frame_pos <= 5'b00111;
			5'b00111 : next_frame_pos <= 5'b00101;
			5'b00101 : next_frame_pos <= 5'b00100;
			5'b00100 : next_frame_pos <= 5'b01100;
			5'b01100 : next_frame_pos <= 5'b11100;
			5'b11100 : next_frame_pos <= 5'b10100;
			5'b10100 : next_frame_pos <= 5'b10101;
			5'b10101 : next_frame_pos <= 5'b10111;
			5'b10111 : next_frame_pos <= 5'b10110;
			5'b10110 : next_frame_pos <= 5'b10010;
			5'b10010 : next_frame_pos <= 5'b10011;
			5'b10011 : next_frame_pos <= 5'b10001;
			5'b10001 : next_frame_pos <= 5'b10000;
			5'b10000 : next_frame_pos <= 5'b00000;
			default : next_frame_pos <= 5'b00000;
		endcase
	end	
	
	always @(posedge SRT_TICK)
	begin
		frame_pos <= next_frame_pos;
	end
	
	always @(posedge PWM_TIMER_TICK)
	begin
		frame_pos_sync <= frame_pos;
	end
	
	always @*
	begin
		case (frame_pos_sync)
			5'b00000 : LEDR <= { pchs[9], pchs[8], pchs[7], pchs[6], pchs[5], pchs[4], pchs[3], pchs[2], pchs[1], pchs[0] };
			5'b00001 : LEDR <= { pchs[8], pchs[9], pchs[6], pchs[5], pchs[4], pchs[3], pchs[2], pchs[1], pchs[0], pchs[0] };
			5'b00011 : LEDR <= { pchs[7], pchs[8], pchs[9], pchs[4], pchs[3], pchs[2], pchs[1], pchs[0], pchs[0], pchs[0] };
			5'b00010 : LEDR <= { pchs[6], pchs[7], pchs[8], pchs[9], pchs[2], pchs[1], pchs[0], pchs[0], pchs[0], pchs[0] };
			5'b00110 : LEDR <= { pchs[5], pchs[6], pchs[7], pchs[8], pchs[9], pchs[0], pchs[0], pchs[0], pchs[0], pchs[0] };
			5'b00111 : LEDR <= { pchs[4], pchs[5], pchs[6], pchs[7], pchs[8], pchs[9], pchs[0], pchs[0], pchs[0], pchs[0] };
			5'b00101 : LEDR <= { pchs[3], pchs[4], pchs[5], pchs[6], pchs[7], pchs[8], pchs[9], pchs[0], pchs[0], pchs[0] };
			5'b00100 : LEDR <= { pchs[2], pchs[3], pchs[4], pchs[5], pchs[6], pchs[7], pchs[8], pchs[9], pchs[0], pchs[0] };
			5'b01100 : LEDR <= { pchs[1], pchs[2], pchs[3], pchs[4], pchs[5], pchs[6], pchs[7], pchs[8], pchs[9], pchs[0] };
			5'b11100 : LEDR <= { pchs[0], pchs[1], pchs[2], pchs[3], pchs[4], pchs[5], pchs[6], pchs[7], pchs[8], pchs[9] };
			5'b10100 : LEDR <= { pchs[0], pchs[0], pchs[1], pchs[2], pchs[3], pchs[4], pchs[5], pchs[6], pchs[9], pchs[8] };
			5'b10101 : LEDR <= { pchs[0], pchs[0], pchs[0], pchs[1], pchs[2], pchs[3], pchs[4], pchs[9], pchs[8], pchs[7] };
			5'b10111 : LEDR <= { pchs[0], pchs[0], pchs[0], pchs[0], pchs[1], pchs[2], pchs[9], pchs[8], pchs[7], pchs[6] };
			5'b10110 : LEDR <= { pchs[0], pchs[0], pchs[0], pchs[0], pchs[0], pchs[9], pchs[8], pchs[7], pchs[6], pchs[5] };
			5'b10010 : LEDR <= { pchs[0], pchs[0], pchs[0], pchs[0], pchs[9], pchs[8], pchs[7], pchs[6], pchs[5], pchs[4] };
			5'b10011 : LEDR <= { pchs[0], pchs[0], pchs[0], pchs[9], pchs[8], pchs[7], pchs[6], pchs[5], pchs[4], pchs[3] };
			5'b10001 : LEDR <= { pchs[0], pchs[0], pchs[9], pchs[8], pchs[7], pchs[6], pchs[5], pchs[4], pchs[3], pchs[2] };
			5'b10000 : LEDR <= { pchs[0], pchs[9], pchs[8], pchs[7], pchs[6], pchs[5], pchs[4], pchs[3], pchs[2], pchs[1] };
			default  : LEDR <= { pchs[0], pchs[9], pchs[8], pchs[7], pchs[5], pchs[4], pchs[3], pchs[2], pchs[1], pchs[0] };
		endcase
	end
	

endmodule