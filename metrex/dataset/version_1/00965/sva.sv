// Bind these assertions into the DUT
bind FSM_INPUT_ENABLE FSM_INPUT_ENABLE_sva sva();

module FSM_INPUT_ENABLE_sva;
  // Local shorthand to improve readability
  wire rst = FSM_sequential_state_reg_reg_1_0;
  wire [1:0] in2 = FSM_sequential_state_reg_reg_2_0;
  wire in2_all = in2[1] & in2[0];

  default clocking cb @(posedge CLK); endclocking

  // Combinational/derivation checks
  assert property (out == state_reg[1]);
  assert property (D == out);
  assert property (E == 1'b0);
  assert property (\FSM_sequential_state_reg_1_i_1_n_0  == state_reg[0]);
  assert property (\FSM_sequential_state_reg_0_i_1_n_0  == (state_reg[0] & (state_reg[1] | in2_all)));
  assert property (\FSM_sequential_state_reg_2_i_1_n_0  == (state_reg[0] & state_reg[1]));

  // Synchronous reset behavior
  assert property (rst |-> (state_reg == 2'b00 && out==1'b0 && D==1'b0 && E==1'b0));

  // Next-state relations
  assert property (!$past(rst) |-> state_reg[1] == $past(state_reg[0]));
  assert property (!$past(rst) |-> state_reg[0] == ($past(state_reg[0]) & ($past(state_reg[1]) | $past(in2_all))));

  // State transition sanity (derivable from next-state, kept concise)
  assert property (!$past(rst) && $past(state_reg==2'b00) |-> state_reg==2'b00);
  assert property (!$past(rst) && $past(state_reg==2'b11) |-> state_reg==2'b11);
  assert property (!$past(rst) && $past(state_reg==2'b10) |-> state_reg==2'b00);
  assert property (!$past(rst) && $past(state_reg==2'b01) &&  $past(in2_all)  |-> state_reg==2'b11);
  assert property (!$past(rst) && $past(state_reg==2'b01) && !$past(in2_all)  |-> state_reg==2'b10);

  // No X on key state/outputs
  assert property (!$isunknown({state_reg,out,D,E}));

  // Coverage: visit all states and key paths
  cover property (state_reg==2'b00);
  cover property (state_reg==2'b01);
  cover property (state_reg==2'b10);
  cover property (state_reg==2'b11);
  cover property (!rst && state_reg==2'b01 && in2_all ##1 state_reg==2'b11);
  cover property (!rst && state_reg==2'b01 && !in2_all ##1 state_reg==2'b10 ##1 state_reg==2'b00);
  cover property ($rose(out));
  cover property (state_reg==2'b11 [*2]);
endmodule