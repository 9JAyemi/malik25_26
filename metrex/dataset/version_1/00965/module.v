
module FSM_INPUT_ENABLE
   (out,
    E,
    D,
    CLK,
    FSM_sequential_state_reg_reg_1_0 ,
    FSM_sequential_state_reg_reg_2_0 );
  output [0:0]out;
  output [0:0]E;
  output [0:0]D;
  input CLK;
  input [0:0]FSM_sequential_state_reg_reg_1_0 ;
  input [1:0]FSM_sequential_state_reg_reg_2_0 ;

  reg [2-1:0]state_reg;

  wire [0:0]D;
  wire [0:0]E;
  wire \FSM_sequential_state_reg_0_i_1_n_0 ;
  wire \FSM_sequential_state_reg_1_i_1_n_0 ;
  wire \FSM_sequential_state_reg_2_i_1_n_0 ;

  assign FSM_sequential_state_reg_0_i_1_n_0   = (state_reg[0] & state_reg[1] & out) | ((~ state_reg[0]) & (~ state_reg[1]) & out) | (state_reg[0] & (~ state_reg[1]) & (~ out) & FSM_sequential_state_reg_reg_2_0[1] & FSM_sequential_state_reg_reg_2_0[0]);
  assign FSM_sequential_state_reg_1_i_1_n_0   = (state_reg[0] & state_reg[1] & out) | ((~ state_reg[0]) & (~ state_reg[1]) & out) | (state_reg[0] & (~ state_reg[1]) & (~ out));
  assign FSM_sequential_state_reg_2_i_1_n_0   = (state_reg[0] & state_reg[1] & out) | ((~ state_reg[0]) & (~ state_reg[1]) & out) | ((~ state_reg[0]) & state_reg[1] & (~ out));
  assign D = out;
  assign E = state_reg[0] & (~ out) & state_reg[1];
  assign out = state_reg[2-1];

  always @(posedge CLK) begin
    if (FSM_sequential_state_reg_reg_1_0 ) begin
      state_reg[0] <= 1'b0;
      state_reg[1] <= 1'b0;
    end else begin
      state_reg[0] <= FSM_sequential_state_reg_0_i_1_n_0 ;
      state_reg[1] <= FSM_sequential_state_reg_1_i_1_n_0 ;
    end
  end
endmodule