// SVA checker for flip_flop
module flip_flop_sva (
  input logic CLK,
  input logic D,
  input logic SCD,
  input logic SCE,
  input logic Q,
  input logic Q_N,
  input logic VPWR,
  input logic VGND
);

  default clocking cb @(posedge CLK); endclocking

  // Complement output must always match
  a_complement: assert property (@(posedge Q or negedge Q or posedge Q_N or negedge Q_N) Q_N === ~Q);

  // Power rails sane
  a_power_ok:   assert property (cb VPWR===1'b1 && VGND===1'b0);

  // No X/Z on key signals at clock
  a_inputs_known:  assert property (cb !$isunknown({SCD,SCE,D}));
  a_outputs_known: assert property (cb !$isunknown({Q,Q_N}));

  // Functional next-state check (priority: SCD > SCE > D)
  a_next_state: assert property (cb
    !$isunknown($past({SCD,SCE,D})) |-> 
      Q == ($past(SCD) ? 1'b0 : ($past(SCE) ? 1'b1 : $past(D)))
  );

  // Q may only change in conjunction with a CLK rising edge
  a_q_changes_only_on_clk: assert property (@(posedge Q or negedge Q) $rose(CLK));

  // Coverage: exercise all branches and both Q transitions
  cv_clear:  cover property (cb $past(SCD));
  cv_set:    cover property (cb !$past(SCD) && $past(SCE));
  cv_load0:  cover property (cb !$past(SCD) && !$past(SCE) && $past(D)==1'b0);
  cv_load1:  cover property (cb !$past(SCD) && !$past(SCE) && $past(D)==1'b1);
  cv_both:   cover property (cb $past(SCD) && $past(SCE)); // priority case
  cv_q_rise: cover property (@(posedge Q) 1);
  cv_q_fall: cover property (@(negedge Q) 1);

endmodule

// Bind into DUT
bind flip_flop flip_flop_sva u_flip_flop_sva (
  .CLK(CLK),
  .D(D),
  .SCD(SCD),
  .SCE(SCE),
  .Q(Q),
  .Q_N(Q_N),
  .VPWR(VPWR),
  .VGND(VGND)
);