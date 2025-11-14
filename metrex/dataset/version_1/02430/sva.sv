// SVA for SNPS_CLOCK_GATE_HIGH_RegisterAdd_W32_0_7
// Focused, concise checks + coverage

module cg_sva;
  // Bound into SNPS_CLOCK_GATE_HIGH_RegisterAdd_W32_0_7 scope
  default clocking cb @(posedge CLK); endclocking

  // Structural wiring correctness
  a_ck_wiring: assert property (CK === CLK);
  a_e_wiring:  assert property (E  === TE);
  a_se_wiring: assert property (SE === EN);

  // Combinational gate equation must hold continuously
  a_gate_eq: assert property (@(posedge EN or negedge EN or
                                posedge ECK or negedge ECK or
                                posedge ENCLK or negedge ENCLK)
                              ENCLK === (EN & ECK));

  // Sequential capture and hold behavior of the latch/flop
  a_cap:  assert property (SE |-> (ECK == $past(TE)));
  a_hold: assert property (!SE |-> (ECK == $past(ECK)));

  // ECK can only change on a CLK rising edge
  a_eck_only_on_clk: assert property (@(posedge ECK or negedge ECK) $rose(CLK));

  // ENCLK changes only due to EN or ECK changes (no spurious glitches)
  a_enclk_change_cause: assert property (@(posedge ENCLK or negedge ENCLK)
                                         ($changed(EN) || $changed(ECK)));

  // Key outputs should not go X/Z
  a_no_x_out: assert property (!$isunknown({ENCLK, ECK}));

  // Coverage: exercise key modes and edges
  c_en_low_gates_zero:    cover property (@(negedge EN) ENCLK == 1'b0);
  c_en_high_passes_one:   cover property (@(posedge EN) ECK ##0 ENCLK);
  c_cap_one:              cover property (SE && TE    ##1 ECK);
  c_cap_zero:             cover property (SE && !TE   ##1 !ECK);
  c_eck_toggles_with_clk: cover property (SE ##1 $changed(ECK));
  c_enclk_follow_up:      cover property (@(posedge ECK)  EN && ENCLK);
  c_enclk_follow_down:    cover property (@(negedge ECK)  EN && !ENCLK);
endmodule

bind SNPS_CLOCK_GATE_HIGH_RegisterAdd_W32_0_7 cg_sva cg_sva_i();