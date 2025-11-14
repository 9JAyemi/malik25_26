// SVA for and_gate
// Bind this file to the DUT: bind and_gate and_gate_sva sva_i(.*);

module and_gate_sva (
  input logic CLK,
  input logic D,
  input logic SCD,
  input logic SCE,
  input logic SET_B,
  input logic VPWR,
  input logic VGND,
  input logic Q,
  input logic Q_N
);

  default clocking cb @(posedge CLK); endclocking

  // Common terms
  let and_term = (D & SCD & SET_B & VPWR & VGND);
  let exp_q    = (SCE ? and_term : 1'b0);

  // Functional correctness (under known inputs)
  property p_func;
    !$isunknown({D,SCD,SCE,SET_B,VPWR,VGND}) |-> (Q === exp_q);
  endproperty
  assert property (p_func);

  // Complement output correctness
  property p_qn_is_notq;
    !$isunknown(Q) |-> (Q_N === ~Q);
  endproperty
  assert property (p_qn_is_notq);

  // If inputs are known, outputs must be known
  assert property( !$isunknown({D,SCD,SCE,SET_B,VPWR,VGND}) |-> !$isunknown({Q,Q_N}) );

  // Strong implications for easy debug
  assert property( (SCE === 1'b0) |-> (Q === 1'b0) );        // gating off forces Q=0
  assert property( (Q === 1'b1) |-> (SCE && and_term) );     // Q high implies all gating high

  // Coverage: key behaviors exercised
  cover property (SCE===1'b0 && Q===1'b0);                   // gated low case
  cover property (SCE && and_term && Q===1'b1);              // all-high case drives Q=1
  cover property (SCE && $rose(Q));                          // observe Q rising when enabled
  cover property (SCE && $fell(Q));                          // observe Q falling when enabled
  cover property (Q===1'b0 && Q_N===1'b1);                   // complement state 0/1
  cover property (Q===1'b1 && Q_N===1'b0);                   // complement state 1/0
  cover property ($rose(SCE) && (Q === and_term));           // enable edge reflects combinational result
  cover property ($fell(SCE) && (Q === 1'b0));               // disable edge forces Q low

endmodule