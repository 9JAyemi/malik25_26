// SVA for DeBounce
// Bind into DUT scope so we can see internals (DFF1/DFF2/q_reg/q_add/q_reset)
bind DeBounce DeBounce_sva #(.N(N)) u_DeBounce_sva();

module DeBounce_sva #(parameter int N = 11) ();
  // Access DUT scope signals directly (bound into DeBounce)
  // clk, n_reset, button_in, DB_out, DFF1, DFF2, q_reg, q_add, q_reset exist in bind scope
  localparam int SAT = (1 << (N-1));

  default clocking cb @(posedge clk); endclocking

  // Combinational wire correctness
  a_qreset_def: assert property (q_reset == (DFF1 ^ DFF2));
  a_qadd_def:   assert property (q_add   == ~q_reg[N-1]);

  // Synchronous reset behavior
  a_reset_clr_regs: assert property (!n_reset |-> (DFF1==1'b0 && DFF2==1'b0 && q_reg=='0));

  // Counter next-state (use one-cycle history guards)
  a_qreg_reset_on_qreset: assert property (n_reset && $past(n_reset) && $past(q_reset) |-> (q_reg=='0));
  a_qreg_inc_when_msb0:   assert property (n_reset && $past(n_reset) && !$past(q_reset) && !$past(q_reg[N-1])
                                           |-> q_reg == $past(q_reg)+1);
  a_qreg_hold_when_msb1:  assert property (n_reset && $past(n_reset) && !$past(q_reset) &&  $past(q_reg[N-1])
                                           |-> q_reg == $past(q_reg));

  // Two-flop synchronizer: 2-cycle latency from button_in to DFF2 (outside of reset)
  a_sync2_delay: assert property (n_reset && $past(n_reset,1) && $past(n_reset,2)
                                  |-> DFF2 == $past(button_in,2));

  // DB_out update semantics (uses pre-update conditions/RHS)
  a_dbout_exact_update: assert property (n_reset && $past(n_reset)
                                         |-> DB_out == ($past(q_reg[N-1]) ? $past(DFF2) : $past(DB_out)));
  a_dbout_changes_only_when_msb1: assert property (n_reset && $past(n_reset) && (DB_out != $past(DB_out))
                                                   |-> $past(q_reg[N-1]));

  // Useful coverage
  c_counter_saturates: cover property (disable iff(!n_reset)
                                       !q_reg[N-1] && !q_reset
                                       ##1 (!q_reset && !q_reg[N-1])[* (SAT-1)]
                                       ##1 q_reg[N-1]);
  c_dbout_rise: cover property (disable iff(!n_reset) $rose(DB_out));
  c_dbout_fall: cover property (disable iff(!n_reset) $fell(DB_out));
  c_qreset_seen: cover property (disable iff(!n_reset) $rose(q_reset));
endmodule