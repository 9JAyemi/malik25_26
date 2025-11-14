
module FSM_Mult_Function(
	input wire clk,
	input wire rst,
	input wire beg_FSM, input wire ack_FSM, input wire zero_flag_i,
	
	input wire Mult_shift_i,
	
	input wire round_flag_i,
	
	input wire Add_Overflow_i,

	output reg load_0_o, 

	
	output reg load_1_o, 

	output reg load_2_o, 
	
	output reg load_3_o, 
	
	output reg load_4_o,
	
	output reg load_5_o,

	output reg load_6_o,
	

	output reg ctrl_select_a_o,
	output reg ctrl_select_b_o,
	output reg [1:0] selector_b_o,
	output reg ctrl_select_c_o,
	

	output reg exp_op_o,

	output reg shift_value_o,

	output reg rst_int,
		output reg ready
    );


parameter [3:0] start = 4'd0,load_operands = 4'd1, extra64_1 = 4'd2,

add_exp = 4'd3, subt_bias = 4'd4, mult_overf= 4'd5, mult_norn = 4'd6, mult_no_norn = 4'd7, round_case = 4'd8, adder_round =  4'd9, round_norm = 4'd10, final_load = 4'd11, ready_flag = 4'd12; reg [3:0] state_reg, state_next;

always @(posedge clk, posedge rst)
	if(rst)
		state_reg <= start;
	else
		state_reg <= state_next;

always @*
	begin
	state_next = state_reg; load_0_o=0;

	
	 load_1_o=0;

	load_2_o=0; 
	
	load_3_o=0; 
	
	load_4_o=0;
	
	load_5_o=0;

	 load_6_o=0;
	 
	ctrl_select_a_o=0;
	 ctrl_select_b_o=0;
	 selector_b_o=2'b0;
	 ctrl_select_c_o=0;
	

	exp_op_o=0;

	shift_value_o=0;

	rst_int=0;
		ready=0;
	
	case(state_reg)
		start:
		begin
			rst_int = 1;
			if(beg_FSM)
				state_next = load_operands; end
		load_operands:
		begin
			load_0_o = 1;
			state_next = extra64_1;
		end
		
		extra64_1:
		begin
		  state_next = add_exp;
        end
		
		add_exp:
		begin
			load_1_o = 1;
			load_2_o = 1;
			ctrl_select_a_o = 1;
			ctrl_select_b_o = 1;
			selector_b_o = 2'b01;
			state_next = subt_bias;
		end
		subt_bias:
		begin
			load_2_o = 1;
			load_3_o = 1;
			exp_op_o = 1;

			if(zero_flag_i)
				state_next = ready_flag;
			else
				state_next = mult_overf;

		end
		mult_overf:
		begin
			if(Mult_shift_i) begin
				ctrl_select_b_o =1;
				selector_b_o =2'b10;
				state_next = mult_norn;
			end
			else
				state_next = mult_no_norn;
		end
		mult_norn:
		begin
			shift_value_o =1;
			load_6_o = 1;
			load_2_o = 1;
			load_3_o = 1;
			state_next = round_case;
		end
		mult_no_norn:
		begin
			shift_value_o =0;
			load_6_o = 1;
			state_next = round_case;
		end
		round_case:
		begin
			if(round_flag_i) begin
				ctrl_select_c_o =1;
				state_next = adder_round;
			end
			else
				state_next = final_load;
		end
		adder_round:
		begin
			load_4_o = 1;
			ctrl_select_b_o = 1;
			selector_b_o = 2'b01;
			state_next = round_norm;
		end
		round_norm:
		begin
			load_6_o = 1;
			if(Add_Overflow_i)begin
				shift_value_o =1;
				load_2_o = 1;
				load_3_o = 1;
				state_next = final_load;
			end
			else begin
				shift_value_o =0;
				state_next = final_load;
			end
		end
		
		final_load: 
		begin
			load_5_o =1;
			state_next = ready_flag;
		end
		ready_flag:
		begin
			ready = 1;
				if(ack_FSM) begin
					state_next = start;end
		end
		
		default:
		begin
			state_next =start;end
	endcase
end
				
		
endmodule
