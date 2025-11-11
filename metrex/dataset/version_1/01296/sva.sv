// Bind these assertions into every instance of the DUT
bind pcie3_7x_0_qpll_reset pcie3_7x_0_qpll_reset_sva #(
  .PCIE_PLL_SEL(PCIE_PLL_SEL),
  .PCIE_POWER_SAVING(PCIE_POWER_SAVING),
  .PCIE_LANE(PCIE_LANE),
  .BYPASS_COARSE_OVRD(BYPASS_COARSE_OVRD)
) u_pcie3_7x_0_qpll_reset_sva();

// SVA module (elaborated in DUT scope; internal regs/states are visible)
module pcie3_7x_0_qpll_reset_sva #(
  parameter string PCIE_PLL_SEL       = "CPLL",
  parameter string PCIE_POWER_SAVING  = "TRUE",
  parameter int    PCIE_LANE          = 1,
  parameter int    BYPASS_COARSE_OVRD = 1
) ();

  default clocking cb @(posedge QRST_CLK); endclocking

  // Reset-time state/output values (synchronous reset)
  assert property (@(posedge QRST_CLK)
    (!QRST_RST_N) |-> (
      (fsm==FSM_WAIT_LOCK) &&
      (ovrd==1'b0) && (qpllreset==1'b1) && (qpllpd==1'b0) &&
      (QRST_OVRD==1'b0) &&
      (QRST_DRP_START==1'b0) &&
      (QRST_QPLLRESET_OUT==1'b1) &&
      (QRST_IDLE==1'b0) &&
      (QRST_FSM==FSM_WAIT_LOCK) &&
      ((PCIE_POWER_SAVING=="FALSE") ? (QRST_QPLLPD_OUT==1'b0) : (QRST_QPLLPD_OUT==qpllpd))
    )
  );

  default disable iff (!QRST_RST_N)

  // One-hot FSM encoding
  assert property ($onehot(fsm));

  // Output decodes
  assert property (QRST_OVRD==ovrd);
  assert property (QRST_QPLLRESET_OUT==qpllreset);
  assert property (QRST_IDLE==(fsm==FSM_IDLE));
  assert property (QRST_FSM==fsm);
  assert property (QRST_DRP_START == ((fsm==FSM_DRP_START_NOM) || (fsm==FSM_DRP_START_OPT)));
  assert property (
    (PCIE_POWER_SAVING=="FALSE") ? (QRST_QPLLPD_OUT==1'b0) : (QRST_QPLLPD_OUT==qpllpd)
  );

  // Two-stage input sampling pipeline
  assert property (mmcm_lock_reg1    == $past(QRST_MMCM_LOCK));
  assert property (cplllock_reg1     == $past(QRST_CPLLLOCK));
  assert property (drp_done_reg1     == $past(QRST_DRP_DONE));
  assert property (qplllock_reg1     == $past(QRST_QPLLLOCK));
  assert property (rate_reg1         == $past(QRST_RATE));
  assert property (qpllreset_in_reg1 == $past(QRST_QPLLRESET_IN));
  assert property (qpllpd_in_reg1    == $past(QRST_QPLLPD_IN));

  assert property (mmcm_lock_reg2    == $past(mmcm_lock_reg1));
  assert property (cplllock_reg2     == $past(cplllock_reg1));
  assert property (drp_done_reg2     == $past(drp_done_reg1));
  assert property (qplllock_reg2     == $past(qplllock_reg1));
  assert property (rate_reg2         == $past(rate_reg1));
  assert property (qpllreset_in_reg2 == $past(qpllreset_in_reg1));
  assert property (qpllpd_in_reg2    == $past(qpllpd_in_reg1));

  // FSM transition relation (exactly what RTL encodes)
  assert property ( (fsm==FSM_IDLE)           |=> (fsm==FSM_IDLE) );

  assert property ( (fsm==FSM_WAIT_LOCK)      |=> ((&(~cplllock_reg2)) && (&(~qplllock_reg2)))
                                                ? (fsm==FSM_MMCM_LOCK) : (fsm==FSM_WAIT_LOCK) );

  assert property ( (fsm==FSM_MMCM_LOCK)      |=> (mmcm_lock_reg2 && (&cplllock_reg2))
                                                ? (fsm==FSM_DRP_START_NOM) : (fsm==FSM_MMCM_LOCK) );

  assert property ( (fsm==FSM_DRP_START_NOM)  |=> (&(~drp_done_reg2))
                                                ? (fsm==FSM_DRP_DONE_NOM) : (fsm==FSM_DRP_START_NOM) );

  assert property ( (fsm==FSM_DRP_DONE_NOM)   |=> (&drp_done_reg2)
                                                ? (fsm==FSM_QPLLLOCK) : (fsm==FSM_DRP_DONE_NOM) );

  assert property ( (fsm==FSM_QPLLLOCK)       |=> (&qplllock_reg2)
                                                ? ((BYPASS_COARSE_OVRD==1) ? (fsm==FSM_QPLL_PDRESET)
                                                                            : (fsm==FSM_DRP_START_OPT))
                                                : (fsm==FSM_QPLLLOCK) );

  assert property ( (fsm==FSM_DRP_START_OPT)  |=> (&(~drp_done_reg2))
                                                ? (fsm==FSM_DRP_DONE_OPT) : (fsm==FSM_DRP_START_OPT) );

  assert property ( (fsm==FSM_DRP_DONE_OPT)   |=> (&drp_done_reg2)
                                                ? ((PCIE_PLL_SEL=="QPLL") ? (fsm==FSM_QPLL_RESET)
                                                                           : (fsm==FSM_QPLL_PDRESET))
                                                : (fsm==FSM_DRP_DONE_OPT) );

  assert property ( (fsm==FSM_QPLL_RESET)     |=> (&(~qplllock_reg2))
                                                ? (fsm==FSM_QPLLLOCK2) : (fsm==FSM_QPLL_RESET) );

  assert property ( (fsm==FSM_QPLLLOCK2)      |=> (&qplllock_reg2)
                                                ? (fsm==FSM_IDLE) : (fsm==FSM_QPLLLOCK2) );

  assert property ( (fsm==FSM_QPLL_PDRESET)   |=> (fsm==FSM_QPLL_PD) );
  assert property ( (fsm==FSM_QPLL_PD)        |=> (fsm==FSM_IDLE) );

  // OVRD behavior
  assert property ( (fsm==FSM_DRP_START_OPT) |-> (ovrd==1'b1) );
  assert property ( (fsm!=FSM_DRP_START_OPT) |-> $stable(ovrd) );
  assert property ( ovrd |=> ovrd ); // monotonic until reset

  // qpllreset expectations by state
  assert property ( (fsm==FSM_QPLLLOCK)   |-> (qpllreset==1'b0) );
  assert property ( (fsm==FSM_QPLL_RESET) |-> (qpllreset==1'b1) );
  assert property ( (fsm==FSM_QPLLLOCK2)  |-> (qpllreset==1'b0) );
  assert property ( (fsm==FSM_QPLL_PDRESET)
                    |-> ( qpllreset == ((PCIE_PLL_SEL=="CPLL") ? (rate_reg2!=2'd2) : 1'b0) ) );
  assert property ( (fsm==FSM_IDLE)       |-> ( qpllreset == (&qpllreset_in_reg2) ) );

  // qpllpd expectations by state
  assert property ( (fsm==FSM_IDLE)       |-> ( qpllpd == (&qpllpd_in_reg2) ) );
  assert property ( (fsm==FSM_QPLL_RESET) |-> ( qpllpd == 1'b0 ) );
  assert property ( (fsm==FSM_QPLLLOCK2)  |-> ( qpllpd == 1'b0 ) );
  assert property ( (fsm==FSM_QPLL_PD)    |-> ( qpllpd == ((PCIE_PLL_SEL=="CPLL") ? (rate_reg2!=2'd2) : 1'b0) ) );
  assert property ( !(fsm inside {FSM_IDLE, FSM_QPLL_RESET, FSM_QPLLLOCK2, FSM_QPLL_PD}) |-> $stable(qpllpd) );

  // Minimal but meaningful coverage
  cover property ( (fsm==FSM_WAIT_LOCK) ##1 (fsm==FSM_MMCM_LOCK) ##1
                   (fsm==FSM_DRP_START_NOM) ##1 (fsm==FSM_DRP_DONE_NOM) ##1 (fsm==FSM_QPLLLOCK) );

  if (BYPASS_COARSE_OVRD==1) begin
    cover property ( (fsm==FSM_QPLLLOCK) ##1 (fsm==FSM_QPLL_PDRESET) ##1
                     (fsm==FSM_QPLL_PD) ##1 (fsm==FSM_IDLE) );
  end else begin
    cover property ( (fsm==FSM_QPLLLOCK) ##1 (fsm==FSM_DRP_START_OPT) ##1 (fsm==FSM_DRP_DONE_OPT) );
    if (PCIE_PLL_SEL=="QPLL") begin
      cover property ( (fsm==FSM_DRP_DONE_OPT) ##1 (fsm==FSM_QPLL_RESET) ##1
                       (fsm==FSM_QPLLLOCK2) ##1 (fsm==FSM_IDLE) );
    end else begin
      cover property ( (fsm==FSM_DRP_DONE_OPT) ##1 (fsm==FSM_QPLL_PDRESET) ##1
                       (fsm==FSM_QPLL_PD) ##1 (fsm==FSM_IDLE) );
    end
  end

  cover property ( (fsm==FSM_DRP_START_OPT) and ovrd );

endmodule