// SVA for controller_m
module controller_m_sva #(parameter bit S_Idle=1'b0, S_Mul=1'b1) (
  input  logic clock, reset, start, Zero,
  input  logic Ready, Load_regs, Add_dec,
  input  logic state, next_state
);
  default clocking cb @(posedge clock); endclocking
  default disable iff (reset);

  // Output decodes
  assert property (Ready == (state == S_Idle));
  assert property (Load_regs == ((state == S_Idle) && start));
  assert property (Add_dec == ((state == S_Mul) && !Zero));
  assert property (!(Load_regs && Add_dec));

  // State validity and X checks
  assert property (state inside {S_Idle, S_Mul});
  assert property (!$isunknown(state));
  assert property ($isunknown({start,Zero}) || !$isunknown({Load_regs,Add_dec}));

  // Combinational next_state correctness
  assert property ((state == S_Idle) |-> next_state == (start ? S_Mul : S_Idle));
  assert property ((state == S_Mul)  |-> next_state == ((!Zero) ? S_Idle : S_Mul));

  // Reset behavior
  assert property (@(posedge clock) reset |-> state == S_Idle);

  // Registered state transitions
  assert property ((state==S_Idle &&  start) |=> state==S_Mul);
  assert property ((state==S_Idle && !start) |=> state==S_Idle);
  assert property ((state==S_Mul  && !Zero)  |=> state==S_Idle);
  assert property ((state==S_Mul  &&  Zero)  |=> state==S_Mul);

  // Coverage
  cover property (state==S_Idle && start ##1 state==S_Mul && !Zero ##1 state==S_Idle);
  cover property (state==S_Idle && !start ##1 state==S_Idle);
  cover property (state==S_Mul  &&  Zero  ##1 state==S_Mul);
  cover property (Load_regs);
  cover property (Add_dec);
endmodule

bind controller_m controller_m_sva #(.S_Idle(S_Idle), .S_Mul(S_Mul)) sva_i (.*);