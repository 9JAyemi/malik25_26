// SVA for RegisterAdd
`ifndef REGISTERADD_SVA
`define REGISTERADD_SVA

module RegisterAdd_sva (
  input  logic        clk_IBUF_BUFG,
  input  logic        FSM_selector_C,
  input  logic        AR,
  input  logic [1:0]  FSM_sequential_state_reg_reg
);

  default clocking @(posedge clk_IBUF_BUFG); endclocking

  bit past_valid;
  always @(posedge clk_IBUF_BUFG) past_valid <= 1'b1;

  // Sanity: no X/Z on controls and state
  assert property ( !$isunknown(FSM_selector_C) && !$isunknown(AR) )
    else $error("X/Z detected on control inputs");
  assert property ( !$isunknown(FSM_sequential_state_reg_reg) )
    else $error("X/Z detected on state");

  // Synchronous clear has priority
  assert property ( disable iff (!past_valid)
                    FSM_selector_C |=> (FSM_sequential_state_reg_reg == 2'b00) );

  // Next-state function when not clearing: state = prev_state + AR (mod 4)
  assert property ( disable iff (!past_valid)
                    !FSM_selector_C |=> (FSM_sequential_state_reg_reg
                                         == $past(FSM_sequential_state_reg_reg) + $past(AR)) );

  // Coverage: clear, hold, increment, and wrap-around
  cover property ( disable iff (!past_valid)
                   FSM_selector_C |=> (FSM_sequential_state_reg_reg == 2'b00) );
  cover property ( disable iff (!past_valid)
                   !FSM_selector_C &&  AR |=> (FSM_sequential_state_reg_reg
                                               == $past(FSM_sequential_state_reg_reg) + 2'd1) );
  cover property ( disable iff (!past_valid)
                   !FSM_selector_C && !AR |=> (FSM_sequential_state_reg_reg
                                               == $past(FSM_sequential_state_reg_reg)) );
  cover property ( disable iff (!past_valid)
                   $past(FSM_sequential_state_reg_reg)==2'b11 && !FSM_selector_C && AR
                   |=> (FSM_sequential_state_reg_reg == 2'b00) );

  // Hit all 2-bit states
  cover property (FSM_sequential_state_reg_reg == 2'b00);
  cover property (FSM_sequential_state_reg_reg == 2'b01);
  cover property (FSM_sequential_state_reg_reg == 2'b10);
  cover property (FSM_sequential_state_reg_reg == 2'b11);

endmodule

bind RegisterAdd RegisterAdd_sva
(
  .clk_IBUF_BUFG(clk_IBUF_BUFG),
  .FSM_selector_C(FSM_selector_C),
  .AR(AR),
  .FSM_sequential_state_reg_reg(FSM_sequential_state_reg_reg)
);

`endif