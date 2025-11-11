// SVA for TLATNTSCAX2TS: ECK = (SE ? E : ~E), CK has no effect
module TLATNTSCAX2TS_sva (input E, SE, CK, ECK);
  default clocking cb @(posedge CK); endclocking

  // Truth function holds whenever inputs are known
  ap_tlat_truth: assert property (!$isunknown({E,SE}) |-> (ECK == (SE ? E : ~E)));

  // CK has no effect if E and SE are stable
  ap_ck_noeffect_pos: assert property (@(posedge CK)
                                       (!$isunknown({E,SE,ECK}) && $stable({E,SE}))
                                       |-> (ECK == $past(ECK)));
  ap_ck_noeffect_neg: assert property (@(negedge CK)
                                       (!$isunknown({E,SE,ECK}) && $stable({E,SE}))
                                       |-> (ECK == $past(ECK)));

  // Basic functional coverage
  cp_se_e_11: cover property (SE && E);
  cp_se_e_10: cover property (SE && !E);
  cp_se_e_01: cover property (!SE && E);
  cp_se_e_00: cover property (!SE && !E);
  cp_toggle_se: cover property ($changed(SE));
  cp_toggle_e:  cover property ($changed(E));
  cp_toggle_eck:cover property ($changed(ECK));
endmodule

bind TLATNTSCAX2TS TLATNTSCAX2TS_sva tlat_sva_i (.E(E), .SE(SE), .CK(CK), .ECK(ECK));


// SVA for flipflop: connectivity, truth of Q, and SE_REG behavior
module flipflop_sva (input CLK, D, RESET, EN, Q, E, SE, ECK, SE_REG);
  default clocking cb @(posedge CLK); endclocking

  // Connectivity
  ap_conn_E:    assert property (!$isunknown({E,EN})     |-> (E == EN));
  ap_conn_SE:   assert property (!$isunknown({SE,RESET}) |-> (SE == RESET));
  ap_conn_QECK: assert property (!$isunknown({Q,ECK})    |-> (Q == ECK));

  // Truth of Q
  ap_q_truth:   assert property (!$isunknown({EN,RESET}) |-> (Q == (RESET ? EN : ~EN)));

  // SE_REG update/hold semantics
  ap_se_reg_en:   assert property (EN && !$isunknown(D) |=> (SE_REG == !$past(D)));
  ap_se_reg_hold: assert property (!EN                 |=> (SE_REG == $past(SE_REG)));

  // Initial value of SE_REG
  initial assert (SE_REG === 1'b0);

  // Coverage: exercise both SE_REG write values and hold
  cp_ser_to0: cover property (EN && D  |=> (SE_REG == 1'b0));
  cp_ser_to1: cover property (EN && !D |=> (SE_REG == 1'b1));
  cp_ser_hold: cover property (!EN ##1 (SE_REG == $past(SE_REG)));

  // Coverage: Q behavior under both RESET selections
  cp_q_sel1: cover property (RESET && EN);
  cp_q_sel0: cover property (!RESET && EN);
  cp_q_toggle: cover property ($changed(Q));
endmodule

bind flipflop flipflop_sva ff_sva_i (.CLK(CLK), .D(D), .RESET(RESET), .EN(EN),
                                      .Q(Q), .E(E), .SE(SE), .ECK(ECK), .SE_REG(SE_REG));