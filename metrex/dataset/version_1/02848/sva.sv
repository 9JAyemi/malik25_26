// SVA for Control_Unit. Bind this file to the DUT.
// Focus: reset behavior, output/state mapping, next-state logic, mutual exclusion, X checks, and functional coverage.

module Control_Unit_sva (Control_Unit dut);

  localparam [1:0] S0=2'b00, S1=2'b01, S2=2'b10, S3=2'b11;

  default clocking cb @(posedge dut.clk); endclocking
  default disable iff (!dut.reset_b);

  // Reset cycle effects (checked without disable)
  assert property (@(posedge dut.clk)
    !dut.reset_b |-> (dut.state==S0 && dut.Ld_AR_BR==0 && dut.Mul_BR_x2_CR==0 &&
                      dut.Div_AR_x2_CR==0 && dut.Clr_CR==0 && dut.done==0));

  // Basic sanitation
  assert property (!$isunknown({dut.state, dut.done, dut.Ld_AR_BR, dut.Mul_BR_x2_CR, dut.Div_AR_x2_CR, dut.Clr_CR})));

  // Output mapping per state (Moore behavior)
  assert property ((dut.state==S0) |-> ( dut.Ld_AR_BR && !dut.Mul_BR_x2_CR && !dut.Div_AR_x2_CR && !dut.done && !dut.Clr_CR));
  assert property ((dut.state==S1) |-> (!dut.Ld_AR_BR && !dut.Mul_BR_x2_CR && !dut.Div_AR_x2_CR &&  dut.done && !dut.Clr_CR));
  assert property ((dut.state==S2) |-> (!dut.Ld_AR_BR &&  dut.Mul_BR_x2_CR && !dut.Div_AR_x2_CR &&  dut.done && !dut.Clr_CR));
  assert property ((dut.state==S3) |-> (!dut.Ld_AR_BR && !dut.Mul_BR_x2_CR &&  dut.Div_AR_x2_CR &&  dut.done && !dut.Clr_CR));

  // Simple invariants
  assert property ($onehot0({dut.Ld_AR_BR, dut.Mul_BR_x2_CR, dut.Div_AR_x2_CR})); // at most one control high
  assert property (dut.done == (dut.state!=S0));
  assert property (dut.Clr_CR==0);

  // Next-state logic
  // S0: wait for start
  assert property ((dut.state==S0 && dut.start)     |=> dut.state==S1);
  assert property ((dut.state==S0 && !dut.start)    |=> dut.state==S0);

  // S1: compare AR flags (priority: AR_gt_0 over AR_lt_0)
  assert property ((dut.state==S1 && dut.AR_gt_0)                       |=> dut.state==S2);
  assert property ((dut.state==S1 && !dut.AR_gt_0 && dut.AR_lt_0)       |=> dut.state==S3);
  assert property ((dut.state==S1 && !dut.AR_gt_0 && !dut.AR_lt_0)      |=> dut.state==S1);
  assert property ((dut.state==S1 && dut.AR_gt_0 && dut.AR_lt_0)        |=> dut.state==S2);

  // S2/S3: single-cycle actions then back to S0
  assert property ((dut.state==S2) |=> dut.state==S0);
  assert property ((dut.state==S3) |=> dut.state==S0);

  // Functional coverage
  cover property (dut.state==S0 ##1 dut.start ##1 dut.state==S1 ##1 dut.AR_gt_0 ##1 dut.state==S2 ##1 dut.state==S0);
  cover property (dut.state==S0 ##1 dut.start ##1 dut.state==S1 ##1 !dut.AR_gt_0 && dut.AR_lt_0 ##1 dut.state==S3 ##1 dut.state==S0);
  cover property (dut.state==S1 && !dut.AR_gt_0 && !dut.AR_lt_0 ##1 dut.state==S1 && !dut.AR_gt_0 && !dut.AR_lt_0);
  cover property (dut.state==S1 && dut.AR_gt_0 && dut.AR_lt_0 ##1 dut.state==S2); // priority case
  cover property (dut.state==S0 && !dut.start ##1 dut.state==S0); // idle hold
  cover property (dut.done==0 ##1 dut.done==1 ##1 dut.done==1 ##1 dut.done==0); // typical done pulse shape

endmodule

bind Control_Unit Control_Unit_sva sva_i(.dut(this));