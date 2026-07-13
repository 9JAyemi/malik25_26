
module RegisterAdd (
    input FSM_selector_C,
    output [1:0] FSM_sequential_state_reg_reg,
    input clk_IBUF_BUFG,
    input AR
);

  reg [1:0] FSM_sequential_state_reg_reg;

  always @(posedge clk_IBUF_BUFG) begin
    if (FSM_selector_C) begin
      FSM_sequential_state_reg_reg <= 2'b00;
    end else begin
      FSM_sequential_state_reg_reg <= FSM_sequential_state_reg_reg + AR;
    end
  end

endmodule