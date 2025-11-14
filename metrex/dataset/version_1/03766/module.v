

module CORDIC_FSM_v2
(
input wire clk,											input wire reset,										input wire beg_FSM_CORDIC,								input wire ACK_FSM_CORDIC,								input wire operation,									input wire exception,
input wire [1:0] shift_region_flag,						input wire [1:0] cont_var,								input wire ready_add_subt,								input wire max_tick_iter, min_tick_iter,				input wire max_tick_var, min_tick_var,					output reg reset_reg_cordic,
output reg ready_CORDIC,								output reg beg_add_subt,								output reg ack_add_subt,								output reg sel_mux_1, sel_mux_3,						output reg [1:0] sel_mux_2,								output reg enab_cont_iter, load_cont_iter,				output reg enab_cont_var,  load_cont_var,				output reg enab_RB1, enab_RB2,							output reg enab_d_ff_Xn, enab_d_ff_Yn, enab_d_ff_Zn,	output reg enab_d_ff_out,enab_dff_5,					output reg enab_RB3,
output reg enab_reg_sel_mux1,enab_reg_sel_mux2,enab_reg_sel_mux3
);

localparam [3:0]    est0 = 4'b0000,
                    est1 = 4'b0001,
                    est2 = 4'b0010,
                    est3 = 4'b0011,
                    est4 = 4'b0100,
                    est5 = 4'b0101, 
                    est6 = 4'b0110,
                    est7 = 4'b0111,
                    est8 = 4'b1000,
                    est9 = 4'b1001,
                    est10 = 4'b1010,
                    est11 = 4'b1011,
					est12 = 4'b1100,
					est13 = 4'b1101;
					

reg [3:0] state_reg, state_next;	always @( posedge clk, posedge reset)
    begin
        if(reset)	state_reg <= est0;
        else		state_reg <= state_next;
    end

always @*
    begin
    state_next = state_reg; ready_CORDIC = 1'b0;
    beg_add_subt = 1'b0;
    ack_add_subt = 1'b0;
    sel_mux_1 = 1'b0;
    sel_mux_2 = 2'b00;
    sel_mux_3 = 1'b0;
    enab_cont_iter = 1'b0;
    load_cont_iter = 1'b0;
    enab_cont_var = 1'b0;
    load_cont_var = 1'b0;
    enab_RB1 = 1'b0;
    enab_RB2 = 1'b0;
    enab_RB3 = 1'b0;
    enab_d_ff_Xn = 1'b0;
    enab_d_ff_Yn = 1'b0;
    enab_d_ff_Zn = 1'b0;
    enab_d_ff_out = 1'b0;
    reset_reg_cordic = 1'b0;
    enab_dff_5 = 1'b0;
    enab_reg_sel_mux1 = 1'b0;
    enab_reg_sel_mux2 = 1'b0;
    enab_reg_sel_mux3 = 1'b0;
    
        case(state_reg)
        est0:
        begin
			reset_reg_cordic = 1'b1;
			enab_reg_sel_mux1 = 1'b1;
            enab_reg_sel_mux2 = 1'b1;
            enab_reg_sel_mux3 = 1'b1;
			state_next = est1;
        end

		est1:
        begin
			if(beg_FSM_CORDIC)
			begin
				state_next = est2;
			end
			else
				state_next = est1;
		end

		est2:
		begin
			enab_RB1 = 1'b1;
			enab_cont_iter = 1'b1;
			load_cont_iter = 1'b1;
			state_next = est3;
		end

        est3:
        begin
            if(min_tick_iter)
				sel_mux_1 =	1'b0;
			else
				sel_mux_1 = 1'b1;
			enab_reg_sel_mux1 = 1'b1;
						
			state_next = est4;
        end

        est4:
        begin
			if(exception)
				state_next = est0;
			else
				state_next = est5;
            enab_RB2 = 1'b1;
        end

        est5:
        begin
			enab_RB3 = 1'b1;
			enab_cont_var = 1'b1;
			load_cont_var = 1'b1;
			state_next = est6;
        end

        est6:
        begin            
			if(max_tick_iter)
			begin
				if(operation == 1'b0)
				begin
					if(shift_region_flag == 2'b00)
						sel_mux_2 = 2'b00;
					else if(shift_region_flag == 2'b01)
						sel_mux_2 = 2'b01;
					else if(shift_region_flag == 2'b10)
						sel_mux_2 = 2'b01;
					else
						sel_mux_2 = 2'b00;
					enab_reg_sel_mux2 = 1'b1;
				end
				
				else
				begin
					if(shift_region_flag == 2'b00)
						sel_mux_2 = 2'b01;
					else if(shift_region_flag == 2'b01)
						sel_mux_2 = 2'b00;
					else if(shift_region_flag == 2'b10)
						sel_mux_2 = 2'b00;
					else
						sel_mux_2 = 2'b01;
					enab_reg_sel_mux2 = 1'b1;
				end
			end
			
			else
				sel_mux_2 = cont_var;
			
			enab_reg_sel_mux2 = 1'b1;	
			state_next = est7;	
        end        
        
        est7:
        begin            
			beg_add_subt = 1'b1;
			state_next = est8;
        end

        est8:
        begin
			if(ready_add_subt)
			begin
				if(max_tick_iter)
				begin
					if(operation == 1'b0)
					begin
						if(shift_region_flag == 2'b00)
							enab_d_ff_Xn = 1'b1;
						else if(shift_region_flag == 2'b01)
							enab_d_ff_Yn = 1'b1;
						else if(shift_region_flag == 2'b10)
							enab_d_ff_Yn = 1'b1;
						else
							enab_d_ff_Xn = 1'b1;
					end
					
					else
					begin
						if(shift_region_flag == 2'b00)
							enab_d_ff_Yn = 1'b1;
						else if(shift_region_flag == 2'b01)
							enab_d_ff_Xn = 1'b1;
						else if(shift_region_flag == 2'b10)
							enab_d_ff_Xn = 1'b1;
						else
							enab_d_ff_Yn = 1'b1;
					end
				end
				
				else
				begin
					if(min_tick_var)
						enab_d_ff_Xn = 1'b1;
					else if(max_tick_var)
						enab_d_ff_Zn = 1'b1;
					else
						enab_d_ff_Yn = 1'b1;
				end
				state_next = est9;
			end
			
			else
				state_next = est8;
        end

        est9:
        begin
			ack_add_subt = 1'b1;
			if(max_tick_iter)
			begin
				state_next = est10;
			end
			else
			begin
				if(max_tick_var)
				begin
					enab_cont_iter = 1'b1;
					state_next = est3;
				end
				
				else
				begin
					enab_cont_var = 1'b1;
					state_next = est6;
				end
			end
        end

        est10:
        begin            
			if(operation == 1'b0)
			begin
				if(shift_region_flag == 2'b00)
					sel_mux_3 = 1'b0;
				else if(shift_region_flag == 2'b01)
					sel_mux_3 = 1'b1;
				else if(shift_region_flag == 2'b10)
					sel_mux_3 = 1'b1;
				else
					sel_mux_3 = 1'b0;
				enab_reg_sel_mux3 = 1'b1;
			end
			
			else
			begin
				if(shift_region_flag == 2'b00)
					sel_mux_3 = 1'b1;
				else if(shift_region_flag == 2'b01)
					sel_mux_3 = 1'b0;
				else if(shift_region_flag == 2'b10)
					sel_mux_3 = 1'b0;
				else
					sel_mux_3 = 1'b1;
				enab_reg_sel_mux3 = 1'b1;
			end
			
			enab_reg_sel_mux3 = 1'b1;
			state_next = est11;
		end	

		est11:
		begin	    
			enab_dff_5 = 1'b1;
			state_next = est12;
		end
		
		est12:
		begin
			enab_d_ff_out = 1'b1;
			state_next = est13;
		end

		est13:
		begin
			ready_CORDIC = 1'b1;
			if(ACK_FSM_CORDIC)
				state_next = est0;
			else
				state_next = est13;
		end
        
        default : state_next = est0;
        endcase
    end
endmodule
