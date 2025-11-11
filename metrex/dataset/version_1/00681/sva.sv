// SVA for CORDIC_FSM_v3
// Bind or insert inside the DUT. Assumes visibility of internal state_reg/state encodings.

module CORDIC_FSM_v3_sva;

  // Default clocking/disable
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Basic state sanity
  assert property (state_reg inside {est0,est1,est2,est3,est4,est5,est6,est7});
  assert property (!$isunknown(state_reg));

  // Async reset effect (on next clk after rising reset)
  assert property (@(posedge clk) $rose(reset) |-> state_reg==est0);

  // Output decode: each output equals its intended state condition
  assert property (reset_reg_cordic     == (state_reg==est0));
  assert property (enab_RB1             == (state_reg==est0 || state_reg==est1));
  assert property (enab_RB2             == (state_reg==est2));
  assert property (enab_RB3             == (state_reg==est3));
  assert property (enab_cont_var        == (state_reg==est4 || state_reg==est6));
  assert property (enab_cont_iter       == (state_reg==est6));
  assert property (beg_add_subt         == (state_reg==est4 || state_reg==est5));
  assert property (ready_CORDIC         == (state_reg==est7));
  assert property (enab_d_ff5_data_out  == ((state_reg==est7) || (state_reg==est6 && max_tick_iter)));

  // No X on key outputs
  assert property (!$isunknown({reset_reg_cordic,ready_CORDIC,beg_add_subt,
                                enab_cont_iter,enab_cont_var,enab_RB1,enab_RB2,
                                enab_RB3,enab_d_ff5_data_out}));

  // Mutual exclusion of RB enables
  assert property ($onehot0({enab_RB3,enab_RB2,enab_RB1}));

  // Next-state transition checks
  assert property (state_reg==est0 |-> ##1 (beg_FSM_CORDIC ? state_reg==est1 : state_reg==est0));
  assert property (state_reg==est1 |-> ##1 state_reg==est2);
  assert property (state_reg==est2 |-> ##1 (exception ? state_reg==est0 : state_reg==est3));
  assert property (state_reg==est3 |-> ##1 state_reg==est4);
  assert property (state_reg==est4 |-> ##1 (max_tick_var ? state_reg==est5 : state_reg==est4));
  assert property (state_reg==est5 |-> ##1 (enab_dff_z ? state_reg==est6 : state_reg==est5));
  assert property (state_reg==est6 |-> ##1 (max_tick_iter ? state_reg==est7 : state_reg==est2));
  assert property (state_reg==est7 |-> ##1 (ACK_FSM_CORDIC ? state_reg==est0 : state_reg==est7));

  // Coherency around est6 branch/output
  assert property ((state_reg==est6 && max_tick_iter)  |-> enab_d_ff5_data_out);
  assert property ((state_reg==est6 && !max_tick_iter) |-> !enab_d_ff5_data_out);

  // Coverage
  cover property (state_reg==est0);
  cover property (state_reg==est1);
  cover property (state_reg==est2);
  cover property (state_reg==est3);
  cover property (state_reg==est4);
  cover property (state_reg==est5);
  cover property (state_reg==est6);
  cover property (state_reg==est7);

  // Full successful transaction (no exception, single iteration)
  cover property (
    state_reg==est0 && beg_FSM_CORDIC ##1
    state_reg==est1 ##1
    state_reg==est2 && !exception ##1
    state_reg==est3 ##1
    state_reg==est4 ##[1:$] (state_reg==est4 && max_tick_var) ##1
    state_reg==est5 ##[1:$] (state_reg==est5 && enab_dff_z) ##1
    state_reg==est6 ##[1:$] (state_reg==est6 && max_tick_iter) ##1
    state_reg==est7 ##1
    state_reg==est7 && ACK_FSM_CORDIC ##1
    state_reg==est0
  );

  // Exception path from est2
  cover property (state_reg==est2 && exception ##1 state_reg==est0);

  // Iteration loop back (est6 -> est2)
  cover property (state_reg==est6 && !max_tick_iter ##1 state_reg==est2);

  // Variable loop stall in est4 for multiple cycles before advancing
  cover property (state_reg==est4 && !max_tick_var ##1 state_reg==est4 && !max_tick_var ##1
                  state_reg==est4 && max_tick_var ##1 state_reg==est5);

  // DFF-Z gate stall in est5 for multiple cycles before advancing
  cover property (state_reg==est5 && !enab_dff_z ##1 state_reg==est5 && !enab_dff_z ##1
                  state_reg==est5 && enab_dff_z ##1 state_reg==est6);

endmodule

bind CORDIC_FSM_v3 CORDIC_FSM_v3_sva sva_inst();