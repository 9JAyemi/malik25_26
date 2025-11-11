

module signal_gen(clk, rst, req, stm_value, rsb, gnt);

	parameter INPUT_PORTS = 3;
	parameter RESET_PORT = 1; parameter RESET_SENS = 0; parameter integer CNT_MAX =  	(INPUT_PORTS == 1) ? 2 :
									((INPUT_PORTS == 2) ? 4 :
									((INPUT_PORTS == 3) ? 8 :
									((INPUT_PORTS == 4) ? 16 :
									((INPUT_PORTS == 5) ? 32 :
									0))));

	input clk;
	input rst;
	input req;
	
	output [INPUT_PORTS-1: 0] stm_value; 
	output rsb;
	output gnt;

	parameter PREV_HALF = 1;
	parameter PREV_MAX = 2;
	
	parameter SIZE = 4;
	parameter IDLE = 4'b0001;
	parameter PREV = 4'b0010;
	parameter CURR = 4'b0100;
	parameter NEXT = 4'b1000;

	wire [INPUT_PORTS-1: 0] stm_value; 
	wire rsb;
	reg [INPUT_PORTS-1: 0] symb_value;
	reg rsb_int;
	reg gnt;
	reg	[SIZE-1:0] state;
	
	integer prev_cnt;
	integer curr_cnt;
	integer next_cnt;
	reg rst_invert;
	
	assign stm_value = symb_value;
	assign rsb = rsb_int;

	always@(posedge clk)
	begin: FSM
		if(rst) begin
			state <= #1 IDLE;
			prev_cnt <= 0;
			curr_cnt <= 0;
			next_cnt <= 0;
			symb_value <= 0;
			gnt <= 1'b0;
			if((RESET_PORT == 1) && (RESET_SENS == 0)) begin
				rsb_int <= 1'b0;
			end
			else begin
				rsb_int <= 1'b1;
			end
			rst_invert <= 1'b0;
		end 
		else begin
			case(state)
				IDLE : 
				begin
					rst_invert <= 1'b0;
					if (req == 1'b1) begin
						if((RESET_PORT == 1) && (RESET_SENS == 0)) begin
							rsb_int <= 1'b0;
						end
						else begin
							rsb_int <= 1'b1;
						end
						state <= #1 PREV;
					end 
					else begin
						gnt <= 1'b0;
						state <= #1 IDLE;
					end
				end
				PREV : 
					if (prev_cnt < (PREV_HALF)) begin
						symb_value <= {INPUT_PORTS{1'b0}}; state <= #1 CURR;
					end 
					else if((prev_cnt >= (PREV_HALF)) && (prev_cnt < PREV_MAX)) begin
						symb_value <= {INPUT_PORTS{1'b1}}; state <= #1 CURR;
					end
					else begin
						symb_value <= {INPUT_PORTS{1'b0}};
						if((RESET_PORT == 1) && (RESET_SENS == 0)) begin
							if(rst_invert == 1'b0) begin
								rsb_int <= 1'b1;
								rst_invert <= 1'b1;
								prev_cnt <= 0; state <= #1 CURR;
							end
							else begin
								rsb_int <= 1'b0;
								rst_invert <= 1'b0;
								gnt <= 1'b1;
								state <= #1 IDLE;
							end
						end
						else if((RESET_PORT == 1) && (RESET_SENS == 1)) begin
							if(rst_invert == 1'b0) begin
								rsb_int <= 1'b0;
								rst_invert <= 1'b1;
								prev_cnt <= 0; state <= #1 CURR;
							end
							else begin
								rsb_int <= 1'b1;
								rst_invert <= 1'b0;
								gnt <= 1'b1;
								state <= #1 IDLE;
							end
						end
						else begin
							rsb_int <= 1'b0;
							gnt <= 1'b1;
							state <= #1 IDLE; end
					end
				CURR : 
					if (curr_cnt < (CNT_MAX-1)) begin
						symb_value <= curr_cnt;
						state <= #1 NEXT;
					end 
					else begin
						symb_value <= curr_cnt;
						state <= #1 NEXT;
					end
				NEXT : 
					if (next_cnt < (CNT_MAX-1)) begin
						symb_value <= next_cnt;
						next_cnt <= next_cnt + 1;
						state <= #1 PREV;
					end 
					else begin
						symb_value <= next_cnt;
						next_cnt <= 0; if (curr_cnt < (CNT_MAX-1)) begin
							curr_cnt <= curr_cnt + 1;
						end
						else begin
							curr_cnt <= 0; if(prev_cnt < PREV_MAX) begin
								prev_cnt <= prev_cnt + 1;
							end
							else begin
								prev_cnt <= 0; end
						end
						state <= #1 PREV;
					end
				default : state <= #1 IDLE;
			endcase
		end
	end

endmodule

