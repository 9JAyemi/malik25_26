

module CORDIC_FSM_v3
(
  input wire clk,											input wire reset,										input wire beg_FSM_CORDIC,								input wire ACK_FSM_CORDIC,								input wire exception,
  input wire max_tick_iter, 			input wire max_tick_var, 				input wire enab_dff_z,

  output reg reset_reg_cordic,
  output reg ready_CORDIC,								output reg beg_add_subt,								output reg enab_cont_iter,				output reg enab_cont_var,				output reg enab_RB1, enab_RB2, enab_RB3,
  output reg enab_d_ff5_data_out
);

localparam [3:0]    est0 = 0,
                    est1 = 1,
                    est2 = 2,
                    est3 = 3,
                    est4 = 4,
                    est5 = 5,
                    est6 = 6,
                    est7 = 7;


reg [3:0] state_reg, state_next;	always @( posedge clk, posedge reset)
    begin
        if(reset)	state_reg <= est0;
        else		state_reg <= state_next;
    end

always @*
    begin
    state_next = state_reg; reset_reg_cordic = 0;
    enab_RB1 = 0;
    enab_RB2 = 0;
    enab_RB3 = 0;
    enab_cont_var  = 0;
    enab_cont_iter = 0;
    enab_d_ff5_data_out = 0;
    ready_CORDIC = 0;
    beg_add_subt = 0;

    case(state_reg)

    est0:
    begin
      reset_reg_cordic = 1'b1;
      enab_RB1 = 1'b1;
      if(beg_FSM_CORDIC) begin
        state_next = est1;
      end else begin
        state_next = est0;
      end
    end

		est1:
		begin
      enab_RB1 = 1'b1;
			state_next = est2;
		end

    est2:
    begin
      enab_RB2 = 1'b1;
			if(exception) begin
				state_next = est0;
			end else begin
				state_next = est3;
      end
    end

    est3:
    begin
      enab_RB3 = 1'b1;
			state_next = est4;
    end

    est4:
    begin
      enab_cont_var = 1'b1; beg_add_subt = 1'b1;
      if (max_tick_var) begin
        state_next = est5;
      end else begin
        state_next = est4;
      end
    end

    est5:
    begin
      beg_add_subt = 1'b1;
      if (enab_dff_z) begin
        state_next = est6;
      end else begin
        state_next = est5;
      end
    end

    est6:
    begin
      enab_cont_iter = 1'b1; enab_cont_var = 1'b1; if (max_tick_iter) begin
        state_next = est7; enab_d_ff5_data_out = 1;
      end else begin
        state_next = est2; end
    end

    est7:
    begin
      ready_CORDIC = 1'b1;
      enab_d_ff5_data_out = 1'b1;
      if(ACK_FSM_CORDIC) begin
        state_next = est0;
      end else begin
        state_next = est7;
      end
    end

    default :
      begin
        state_next = est0;
      end

    endcase
  end
endmodule
