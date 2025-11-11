// SystemVerilog Assertions for pcie_7x_v1_3_qpll_reset
// Drop inside the module (e.g., under `ifdef ASSERT_ON)

`ifdef ASSERT_ON

// Default SVA settings
default clocking cb @(posedge QRST_CLK); endclocking
default disable iff (!QRST_RST_N)

// Basic sanity
a_onehot_fsm:        assert property ($onehot(fsm));
a_no_x_core:         assert property (! $isunknown({fsm,ovrd,qpllreset,qpllpd}));
a_out_map_ovrd:      assert property (QRST_OVRD          == ovrd);
a_out_map_drpstart:  assert property (QRST_DRP_START     == ((fsm==FSM_DRP_START_NOM) || (fsm==FSM_DRP_START_OPT)));
a_out_map_qrst:      assert property (QRST_QPLLRESET_OUT == qpllreset);
a_out_map_qpllpd:    assert property (QRST_QPLLPD_OUT    == ((PCIE_POWER_SAVING=="FALSE") ? 1'b0 : qpllpd));
a_out_map_idle:      assert property (QRST_IDLE          == (fsm==FSM_IDLE));
a_out_map_fsm:       assert property (QRST_FSM           == fsm);

// Reset behavior (synchronous active-low)
a_reset_seq: assert property (!QRST_RST_N ##1
                              (fsm==FSM_WAIT_LOCK && ovrd==1'b0 && qpllreset==1'b1 && qpllpd==1'b0));

// 2-stage input synchronizers hold 1-cycle pipeline relationship when not in reset
a_sync_mmcm:     assert property ($past(QRST_RST_N) |-> (mmcm_lock_reg1==$past(QRST_MMCM_LOCK)    && mmcm_lock_reg2==$past(mmcm_lock_reg1)));
a_sync_cpll:     assert property ($past(QRST_RST_N) |-> (cplllock_reg1==$past(QRST_CPLLLOCK)      && cplllock_reg2==$past(cplllock_reg1)));
a_sync_drpdone:  assert property ($past(QRST_RST_N) |-> (drp_done_reg1==$past(QRST_DRP_DONE)      && drp_done_reg2==$past(drp_done_reg1)));
a_sync_qplllock: assert property ($past(QRST_RST_N) |-> (qplllock_reg1==$past(QRST_QPLLLOCK)      && qplllock_reg2==$past(qplllock_reg1)));
a_sync_rate:     assert property ($past(QRST_RST_N) |-> (rate_reg1    ==$past(QRST_RATE)          && rate_reg2    ==$past(rate_reg1)));
a_sync_qpllrst:  assert property ($past(QRST_RST_N) |-> (qpllreset_in_reg1==$past(QRST_QPLLRESET_IN) && qpllreset_in_reg2==$past(qpllreset_in_reg1)));
a_sync_qpllpd:   assert property ($past(QRST_RST_N) |-> (qpllpd_in_reg1   ==$past(QRST_QPLLPD_IN)    && qpllpd_in_reg2   ==$past(qpllpd_in_reg1)));

// State-specific output constraints
a_idle_outs:         assert property ((fsm==FSM_IDLE)       |-> (qpllreset==(&qpllreset_in_reg2)) && (qpllpd==(&qpllpd_in_reg2)));
a_qplllock_rst0:     assert property ((fsm==FSM_QPLLLOCK)   |-> (qpllreset==1'b0));
a_qpllreset_vals:    assert property ((fsm==FSM_QPLL_RESET) |-> (qpllreset==1'b1 && qpllpd==1'b0));
a_qplllock2_vals:    assert property ((fsm==FSM_QPLLLOCK2)  |-> (qpllreset==1'b0 && qpllpd==1'b0));
a_drp_start_opt_ovrd:assert property ((fsm==FSM_DRP_START_OPT) |-> ovrd);

// QPLL power-down/reset policy vs PLL selection and rate
generate
  if (PCIE_PLL_SEL == "CPLL") begin
    a_pdreset_cpll:  assert property ((fsm==FSM_QPLL_PDRESET) |-> (qpllreset == (rate_reg2 != 2'd2)));
    a_pd_cpll:       assert property ((fsm==FSM_QPLL_PD)      |-> (qpllpd    == (rate_reg2 != 2'd2)));
  end else begin
    a_pdreset_qpll:  assert property ((fsm==FSM_QPLL_PDRESET) |-> (qpllreset == 1'b0));
    a_pd_qpll:       assert property ((fsm==FSM_QPLL_PD)      |-> (qpllpd    == 1'b0));
  end
endgenerate

// Power saving output clamp
generate
  if (PCIE_POWER_SAVING == "FALSE") begin
    a_psave_off_pd0: assert property (QRST_QPLLPD_OUT == 1'b0);
  end
endgenerate

// Allowed next-state transitions
a_wait_lock_adv: assert property ((fsm==FSM_WAIT_LOCK && (&(~cplllock_reg2)) && (&(~qplllock_reg2))) |=> (fsm==FSM_MMCM_LOCK));
a_wait_lock_hold:assert property ((fsm==FSM_WAIT_LOCK && !((&(~cplllock_reg2)) && (&(~qplllock_reg2)))) |=> (fsm==FSM_WAIT_LOCK));

a_mmcm_lock_adv: assert property ((fsm==FSM_MMCM_LOCK && mmcm_lock_reg2 && (&cplllock_reg2)) |=> (fsm==FSM_DRP_START_NOM));
a_mmcm_lock_hold:assert property ((fsm==FSM_MMCM_LOCK && !(mmcm_lock_reg2 && (&cplllock_reg2))) |=> (fsm==FSM_MMCM_LOCK));

a_drp_start_nom_adv: assert property ((fsm==FSM_DRP_START_NOM && (&(~drp_done_reg2))) |=> (fsm==FSM_DRP_DONE_NOM));
a_drp_start_nom_hold:assert property ((fsm==FSM_DRP_START_NOM && !(&(~drp_done_reg2))) |=> (fsm==FSM_DRP_START_NOM));

a_drp_done_nom_adv:  assert property ((fsm==FSM_DRP_DONE_NOM && (&drp_done_reg2)) |=> (fsm==FSM_QPLLLOCK));
a_drp_done_nom_hold: assert property ((fsm==FSM_DRP_DONE_NOM && !(&drp_done_reg2)) |=> (fsm==FSM_DRP_DONE_NOM));

generate
  if (BYPASS_COARSE_OVRD == 1) begin
    a_qplllock_adv_b: assert property ((fsm==FSM_QPLLLOCK && (&qplllock_reg2)) |=> (fsm==FSM_QPLL_PDRESET));
  end else begin
    a_qplllock_adv_nb:assert property ((fsm==FSM_QPLLLOCK && (&qplllock_reg2)) |=> (fsm==FSM_DRP_START_OPT));
  end
endgenerate
a_qplllock_hold:     assert property ((fsm==FSM_QPLLLOCK && !(&qplllock_reg2)) |=> (fsm==FSM_QPLLLOCK));

a_drp_start_opt_adv: assert property ((fsm==FSM_DRP_START_OPT && (&(~drp_done_reg2))) |=> (fsm==FSM_DRP_DONE_OPT));
a_drp_start_opt_hold:assert property ((fsm==FSM_DRP_START_OPT && !(&(~drp_done_reg2))) |=> (fsm==FSM_DRP_START_OPT));

generate
  if (PCIE_PLL_SEL == "QPLL") begin
    a_drp_done_opt_adv_q: assert property ((fsm==FSM_DRP_DONE_OPT && (&drp_done_reg2)) |=> (fsm==FSM_QPLL_RESET));
  end else begin
    a_drp_done_opt_adv_c: assert property ((fsm==FSM_DRP_DONE_OPT && (&drp_done_reg2)) |=> (fsm==FSM_QPLL_PDRESET));
  end
endgenerate
a_drp_done_opt_hold: assert property ((fsm==FSM_DRP_DONE_OPT && !(&drp_done_reg2)) |=> (fsm==FSM_DRP_DONE_OPT));

a_qpll_reset_adv:    assert property ((fsm==FSM_QPLL_RESET  && (&(~qplllock_reg2))) |=> (fsm==FSM_QPLLLOCK2));
a_qpll_reset_hold:   assert property ((fsm==FSM_QPLL_RESET  && !(&(~qplllock_reg2))) |=> (fsm==FSM_QPLL_RESET));

a_qplllock2_adv:     assert property ((fsm==FSM_QPLLLOCK2 && (&qplllock_reg2)) |=> (fsm==FSM_IDLE));
a_qplllock2_hold:    assert property ((fsm==FSM_QPLLLOCK2 && !(&qplllock_reg2)) |=> (fsm==FSM_QPLLLOCK2));

a_qpll_pdreset_adv:  assert property ((fsm==FSM_QPLL_PDRESET) |=> (fsm==FSM_QPLL_PD));
a_qpll_pd_adv:       assert property ((fsm==FSM_QPLL_PD)      |=> (fsm==FSM_IDLE));

// OVRD can only rise in DRP_START_OPT
a_ovrd_rise_only: assert property ($rose(ovrd) |-> $past(fsm)==FSM_DRP_START_OPT);

// Coverage: key flows to IDLE
cover_wait_to_nom: cover property (fsm==FSM_WAIT_LOCK ##1
                                   fsm==FSM_MMCM_LOCK ##1
                                   fsm==FSM_DRP_START_NOM ##1
                                   fsm==FSM_DRP_DONE_NOM ##1
                                   fsm==FSM_QPLLLOCK);

generate
  if (BYPASS_COARSE_OVRD == 0 && PCIE_PLL_SEL == "QPLL") begin
    cover_qpll_path: cover property (fsm==FSM_QPLLLOCK ##1
                                     fsm==FSM_DRP_START_OPT ##1
                                     fsm==FSM_DRP_DONE_OPT ##1
                                     fsm==FSM_QPLL_RESET ##1
                                     fsm==FSM_QPLLLOCK2 ##1
                                     fsm==FSM_IDLE);
  end
  if (BYPASS_COARSE_OVRD == 1 && PCIE_PLL_SEL == "QPLL") begin
    cover_qpll_bypass: cover property (fsm==FSM_QPLLLOCK ##1
                                       fsm==FSM_QPLL_PDRESET ##1
                                       fsm==FSM_QPLL_PD ##1
                                       fsm==FSM_IDLE);
  end
  if (BYPASS_COARSE_OVRD == 0 && PCIE_PLL_SEL == "CPLL") begin
    cover_cpll_path: cover property (fsm==FSM_QPLLLOCK ##1
                                     fsm==FSM_DRP_START_OPT ##1
                                     fsm==FSM_DRP_DONE_OPT ##1
                                     fsm==FSM_QPLL_PDRESET ##1
                                     fsm==FSM_QPLL_PD ##1
                                     fsm==FSM_IDLE);
  end
  if (BYPASS_COARSE_OVRD == 1 && PCIE_PLL_SEL == "CPLL") begin
    cover_cpll_bypass: cover property (fsm==FSM_QPLLLOCK ##1
                                       fsm==FSM_QPLL_PDRESET ##1
                                       fsm==FSM_QPLL_PD ##1
                                       fsm==FSM_IDLE);
  end
endgenerate

// Coverage: observe OVRD assertion and DRP start
cover_ovrd_rise:      cover property ($rose(ovrd));
cover_drp_start_pulse:cover property (QRST_DRP_START);

`endif // ASSERT_ON