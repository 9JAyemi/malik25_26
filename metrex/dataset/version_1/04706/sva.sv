// SVA for flip_flop. Bind this to the DUT.
// Focus: correctness of synchronous behavior, priority, complement, and hazards.

module flip_flop_sva (
  input Q, Q_N, D, SCD, SCE, CLK_N, SET_B, RESET_B
);

  default clocking cb @(posedge CLK_N); endclocking

  // Functional/priority check at the active clock edge
  a_func: assert property (
    Q === ( SCD ? 1'b0
        : (SCE || SET_B) ? 1'b1
        : RESET_B ? 1'b0
        : D )
  );

  // Q_N is the complement of Q (checked on both edges to catch glitches)
  a_qn_compl: assert property (@(posedge CLK_N or negedge CLK_N) Q_N === ~Q);

  // Outputs are never X/Z
  a_no_x: assert property (@(posedge CLK_N or negedge CLK_N) !$isunknown({Q,Q_N}));

  // Q changes only on posedge of CLK_N (no combinational glitches)
  a_q_only_on_posedge: assert property (@(posedge CLK_N or negedge CLK_N)
                                        $changed(Q) |-> $rose(CLK_N));

  // ---------------------------------
  // Coverage: each control path and key precedence interactions
  // ---------------------------------
  c_scd_forces_0:     cover property (SCD && Q==1'b0);
  c_sce_forces_1:     cover property (!SCD && SCE && Q==1'b1);
  c_setb_forces_1:    cover property (!SCD && !SCE && SET_B && Q==1'b1);
  c_resetb_forces_0:  cover property (!SCD && !SCE && !SET_B && RESET_B && Q==1'b0);
  c_pass_d_0:         cover property (!SCD && !SCE && !SET_B && !RESET_B && Q==1'b0 && D==1'b0);
  c_pass_d_1:         cover property (!SCD && !SCE && !SET_B && !RESET_B && Q==1'b1 && D==1'b1);

  // Precedence scenarios when multiple controls asserted
  c_pri_scd_over_others: cover property (SCD && (SCE || SET_B || RESET_B) && Q==1'b0);
  c_pri_sce_over_reset:  cover property (!SCD && SCE && RESET_B && Q==1'b1);
  c_pri_set_over_reset:  cover property (!SCD && !SCE && SET_B && RESET_B && Q==1'b1);

  // Toggle coverage
  c_q_rise: cover property ($rose(Q));
  c_q_fall: cover property ($fell(Q));

endmodule

bind flip_flop flip_flop_sva i_flip_flop_sva (
  .Q(Q), .Q_N(Q_N), .D(D), .SCD(SCD), .SCE(SCE),
  .CLK_N(CLK_N), .SET_B(SET_B), .RESET_B(RESET_B)
);