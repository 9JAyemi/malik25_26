module uart_light_tx_ctrl
#(
	parameter STATE_COUNT = 2,
	parameter IDLE = 2'b00,
	parameter LOAD = 2'b01,
	parameter TRANSMITTING = 2'b10
)(
	input  wire reset,
	input  wire clk_tx,

	//Interfaces zum SPMC
	input  wire word_ready,
	output wire fifo_tx_full,
	output wire fifo_tx_empty,
	
	//Interfaces zum Datenpfad-Module, welche durch clk_tx getrieben werden
	input  wire frame_done,
	output reg  transmit,
	output reg  clear,
	output reg  fifo_read_enable,
	
	//Interfaces zum Datenpfad-Module, welche durch clk_peri getrieben werden
	input wire  fifo_full,
	input wire  fifo_empty,
	output wire fifo_write_enable

    );

	reg [STATE_COUNT-1:0] state_cur, state_next;
	
	assign fifo_tx_full      = fifo_full;
	assign fifo_tx_empty     = fifo_empty;
 	assign fifo_write_enable = word_ready & (~fifo_full);
	
	always @(*) begin
		transmit         = 1'b0;
		clear            = 1'b0;
		fifo_read_enable = 1'b0;
		state_next       = IDLE;
		
		case(state_cur)
			IDLE:
				if (fifo_empty == 1'b0) begin
					state_next       = LOAD;
				end
			LOAD:
				begin
					fifo_read_enable = 1'b1;
					state_next	 = TRANSMITTING;
				end
			TRANSMITTING:
				if(frame_done) begin
					clear      = 1'b1;
					state_next = IDLE;
				end
				else begin
					transmit   = 1'b1;
					state_next = TRANSMITTING;
				end
			default: state_next = IDLE;
		endcase
	end
	
	always @(posedge clk_tx, posedge reset) begin
		if(reset) begin
			state_cur <= IDLE;
		end
		else begin 
			state_cur <= state_next;
		end
	end
	
endmodule