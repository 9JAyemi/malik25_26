// SVA for cross_domain_signal
// Bind into the DUT so we can see internal regs
bind cross_domain_signal cross_domain_signal_sva sva();

module cross_domain_signal_sva;

  // Register capture checks (use ##0 to see post-NBA values)
  a_reg_cap_A: assert property (@(posedge CLK_A) ##0 (a_send_sync == CLK_A_SEND));
  b_reg_cap_B: assert property (@(posedge CLK_B) ##0 (b_send_sync == CLK_A_SEND));

  // Cross-domain stage sampling checks
  a_to_b_stage: assert property (@(posedge CLK_B) ##0 (a_send_sync_ff == a_send_sync));
  b_to_a_stage: assert property (@(posedge CLK_A) ##0 (b_send_sync_ff == b_send_sync));

  // Output wiring checks
  out_B_wires: assert property (@(posedge CLK_B) (CLK_B_RECV == a_send_sync_ff));
  out_A_wires: assert property (@(posedge CLK_A) (CLK_A_RECV == b_send_sync_ff));

  // Error logic is XNOR of the two domain regs
  err_func_A:  assert property (@(posedge CLK_A) (ERR == (a_send_sync ~^ b_send_sync)));
  err_func_B:  assert property (@(posedge CLK_B) (ERR == (a_send_sync ~^ b_send_sync)));

  // No X/Z propagation on key signals
  no_xz: assert property (@(posedge CLK_A or posedge CLK_B)
                          !$isunknown({a_send_sync, b_send_sync,
                                       a_send_sync_ff, b_send_sync_ff,
                                       CLK_A_RECV, CLK_B_RECV, ERR}));

  // CDC safety assumptions: source stable when destination samples
  // A -> B crossing
  cdc_safe_ab: assume property (@(posedge CLK_B) (a_send_sync == $past(a_send_sync,1,CLK_B)));
  // B -> A crossing
  cdc_safe_ba: assume property (@(posedge CLK_A) (b_send_sync == $past(b_send_sync,1,CLK_A)));

  // Glitch-free outputs: only change on their own clock posedge
  no_glitch_B: assert property (@(negedge CLK_B) $stable(CLK_B_RECV));
  no_glitch_A: assert property (@(negedge CLK_A) $stable(CLK_A_RECV));

  // Convergence if input is held stable: outputs track the held value in next local cycle
  converge_B: assert property (@(posedge CLK_B)
                               (CLK_A_SEND == $past(CLK_A_SEND,1,CLK_B))
                               |-> ##1 (CLK_B_RECV == CLK_A_SEND));
  converge_A: assert property (@(posedge CLK_A)
                               (CLK_A_SEND == $past(CLK_A_SEND,1,CLK_A))
                               |-> ##1 (CLK_A_RECV == CLK_A_SEND));

  // Coverage: exercise both edge directions across both crossings
  cover_ab_rise: cover property (@(posedge CLK_A) $rose(CLK_A_SEND)
                                 ##[1:$] @(posedge CLK_B) (CLK_B_RECV == 1));
  cover_ab_fall: cover property (@(posedge CLK_A) $fell(CLK_A_SEND)
                                 ##[1:$] @(posedge CLK_B) (CLK_B_RECV == 0));

  cover_ba_rise: cover property (@(posedge CLK_A) $rose(CLK_A_SEND)
                                 ##[1:$] @(posedge CLK_A) (CLK_A_RECV == 1));
  cover_ba_fall: cover property (@(posedge CLK_A) $fell(CLK_A_SEND)
                                 ##[1:$] @(posedge CLK_A) (CLK_A_RECV == 0));

  // Coverage: ERR goes both high and low
  cover_err_1: cover property (@(posedge CLK_A or posedge CLK_B) ERR);
  cover_err_0: cover property (@(posedge CLK_A or posedge CLK_B) !ERR);

endmodule