
module d_ff_en_0
   (d_ff3_sign_out,
    FSM_sequential_state_reg,
    Q,
    CLK,
    EN);

  input [1:0] FSM_sequential_state_reg;
  input [0:0] Q;
  input CLK;
  input EN;
  output reg d_ff3_sign_out;

  wire [0:0] D;

  assign D = Q;

  always @ (posedge CLK or negedge EN) begin
    if (!EN) begin
      d_ff3_sign_out <= 1'b0;
    end
    else begin
      d_ff3_sign_out <= D;
    end
  end

endmodule