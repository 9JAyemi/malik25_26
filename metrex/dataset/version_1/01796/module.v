

module early_boot(
	input CLK_I,
	input RST_I,
	
	output reg CYC_O,
	output reg [31:0] DAT_O,
	output reg STB_O,
	output reg WE_O,
	output reg [31:2] ADR_O,
	output [3:0] SEL_O,
	
	input [31:0] DAT_I,
	input ACK_I,
	input ERR_I,
	input RTY_I,
	
	output loading_finished_o
);
assign SEL_O = 4'b1111;

assign loading_finished_o = (state == S_FINISHED) ? 1'b1 : 1'b0;

reg [3:0] state;
reg [9:0] wait_counter;

parameter [3:0]
	S_CHECK_STATUS 		= 4'd0,
	S_CHECK_STATUS_2 	= 4'd1,
	S_CHECK_STATUS_3 	= 4'd2,
	S_SET_SIZE 			= 4'd3,
	S_SET_SIZE_2 		= 4'd4,
	S_SET_CONTROL 		= 4'd5,
	S_SET_CONTROL_2 	= 4'd6,
	S_CHECK_FINISHED	= 4'd7,
	S_CHECK_FINISHED_2	= 4'd8,
	S_CHECK_FINISHED_3	= 4'd9,
	S_FINISHED 			= 4'd10;

always @(posedge CLK_I) begin
	if(RST_I == 1'b1) begin
		CYC_O <= 1'b0;
		DAT_O <= 32'd0;
		STB_O <= 1'b0;
		WE_O <= 1'b0;
		ADR_O <= 30'd0;
		state <= S_CHECK_STATUS;
		wait_counter <= 10'd0;
	end
	else if(state == S_CHECK_STATUS) begin
		CYC_O <= 1'b1;
		DAT_O <= 32'd0;
		STB_O <= 1'b1;
		WE_O <= 1'b0;
		ADR_O <= 30'h30000000;
		
		state <= S_CHECK_STATUS_2;
	end
	else if(state == S_CHECK_STATUS_2) begin
		if(ACK_I == 1'b1) begin
			CYC_O <= 1'b0;
			STB_O <= 1'b0;
			
			if(DAT_I == 32'd2) begin
				state <= S_SET_SIZE;
			end
			else begin
				state <= S_CHECK_STATUS_3;
			end
		end
	end
	else if(state == S_CHECK_STATUS_3) begin
		if(wait_counter == 10'd1023) begin
			wait_counter <= 10'd0;
			state <= S_CHECK_STATUS;
		end
		else wait_counter <= wait_counter + 10'd1;
	end
	else if(state == S_SET_SIZE) begin
		CYC_O <= 1'b1;
		DAT_O <= 32'd2048;
		STB_O <= 1'b1;
		WE_O <= 1'b1;
		ADR_O <= 30'h30000002;
		
		state <= S_SET_SIZE_2;
	end
	else if(state == S_SET_SIZE_2) begin
		if(ACK_I == 1'b1) begin
			CYC_O <= 1'b0;
			STB_O <= 1'b0;
			
			state <= S_SET_CONTROL;
		end
	end
	else if(state == S_SET_CONTROL) begin
		CYC_O <= 1'b1;
		DAT_O <= 32'd2;
		STB_O <= 1'b1;
		WE_O <= 1'b1;
		ADR_O <= 30'h30000003;
		
		state <= S_SET_CONTROL_2;
	end
	else if(state == S_SET_CONTROL_2) begin
		if(ACK_I == 1'b1) begin
			CYC_O <= 1'b0;
			STB_O <= 1'b0;
			
			state <= S_CHECK_FINISHED;
		end
	end
	else if(state == S_CHECK_FINISHED) begin
		CYC_O <= 1'b1;
		DAT_O <= 32'd0;
		STB_O <= 1'b1;
		WE_O <= 1'b0;
		ADR_O <= 30'h30000000;
		
		state <= S_CHECK_FINISHED_2;
	end
	else if(state == S_CHECK_FINISHED_2) begin
		if(ACK_I == 1'b1) begin
			CYC_O <= 1'b0;
			STB_O <= 1'b0;
			
			if(DAT_I == 32'd2) begin state <= S_FINISHED;
			end
			else begin
				state <= S_CHECK_FINISHED_3;
			end
		end
	end
	else if(state == S_CHECK_FINISHED_3) begin
		if(wait_counter == 10'd1023) begin
			wait_counter <= 10'd0;
			state <= S_CHECK_FINISHED;
		end
		else wait_counter <= wait_counter + 10'd1;
	end
	else if(state == S_FINISHED) begin
	end
	
end

endmodule

