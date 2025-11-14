// SVA for pcie_7x_0_core_top_qpll_reset
// Bind into the DUT for full internal visibility.
module pcie_7x_0_core_top_qpll_reset_sva
  #(parameter string PCIE_PLL_SEL="CPLL",
    parameter string PCIE_POWER_SAVING="TRUE",
    parameter int    PCIE_LANE=1,
    parameter int    BYPASS_COARSE_OVRD=1);

  // State encodings (must match DUT)
  localparam int FSM_IDLE          = 1;
  localparam int FSM_WAIT_LOCK     = 2;
  localparam int FSM_MMCM_LOCK     = 3;
  localparam int FSM_DRP_START_NOM = 4;
  localparam int FSM_DRP_DONE_NOM  = 5;
  localparam int FSM_QPLLLOCK      = 6;
  localparam int FSM_DRP_START_OPT = 7;
  localparam int FSM_DRP_DONE_OPT  = 8;
  localparam int FSM_QPLL_RESET    = 9;
  localparam int FSM_QPLLLOCK2     = 10;
  localparam int FSM_QPLL_PDRESET  = 11;
  localparam int FSM_QPLL_PD       = 12;

  default clocking cb @(posedge QRST_CLK); endclocking
  default disable iff (!QRST_RST_N);

  // Reset behavior
  assert property (@(posedge QRST_CLK) !QRST_RST_N |-> (fsm==FSM_WAIT_LOCK && ovrd==1'b0 && qpllreset==1'b1 && qpllpd==1'b0));

  // 2-stage input sampling
  assert property ($past(QRST_RST_N) |-> (
      mmcm_lock_reg1    == $past(QRST_MMCM_LOCK)   &&
      cplllock_reg1     == $past(QRST_CPLLLOCK)    &&
      drp_done_reg1     == $past(QRST_DRP_DONE)    &&
      qplllock_reg1     == $past(QRST_QPLLLOCK)    &&
      rate_reg1         == $past(QRST_RATE)        &&
      qpllreset_in_reg1 == $past(QRST_QPLLRESET_IN)&&
      qpllpd_in_reg1    == $past(QRST_QPLLPD_IN)
  ));
  assert property ($past(QRST_RST_N) |-> (
      mmcm_lock_reg2    == $past(mmcm_lock_reg1)   &&
      cplllock_reg2     == $past(cplllock_reg1)    &&
      drp_done_reg2     == $past(drp_done_reg1)    &&
      qplllock_reg2     == $past(qplllock_reg1)    &&
      rate_reg2         == $past(rate_reg1)        &&
      qpllreset_in_reg2 == $past(qpllreset_in_reg1)&&
      qpllpd_in_reg2    == $past(qpllpd_in_reg1)
  ));

  // Output encodes/decodes
  assert property (QRST_DRP_START == ((fsm==FSM_DRP_START_NOM) || (fsm==FSM_DRP_START_OPT)));
  assert property (QRST_IDLE      == (fsm==FSM_IDLE));
  assert property (QRST_QPLLRESET_OUT == qpllreset);
  assert property (QRST_OVRD == ovrd);
  assert property (QRST_FSM  == fsm);
  assert property (QRST_QPLLPD_OUT == ((PCIE_POWER_SAVING=="FALSE") ? 1'b0 : qpllpd));

  // IDLE pass-through behavior
  assert property ((fsm==FSM_IDLE) |-> (qpllreset == &qpllreset_in_reg2 && qpllpd == &qpllpd_in_reg2));

  // ovrd must never fall during operation
  assert property (!$fell(ovrd));

  // State transition guards and determinism
  // WAIT_LOCK
  assert property ((fsm==FSM_WAIT_LOCK && (&(~cplllock_reg2) && &(~qplllock_reg2))) |=> fsm==FSM_MMCM_LOCK);
  assert property ((fsm==FSM_WAIT_LOCK && !(~&cplllock_reg2 && ~&qplllock_reg2)) |=> fsm==FSM_WAIT_LOCK);

  // MMCM_LOCK
  assert property ((fsm==FSM_MMCM_LOCK && (mmcm_lock_reg2 && &cplllock_reg2)) |=> fsm==FSM_DRP_START_NOM);
  assert property ((fsm==FSM_MMCM_LOCK && !(mmcm_lock_reg2 && &cplllock_reg2)) |=> fsm==FSM_MMCM_LOCK);

  // DRP_START_NOM
  assert property ((fsm==FSM_DRP_START_NOM && &(~drp_done_reg2)) |=> fsm==FSM_DRP_DONE_NOM);
  assert property ((fsm==FSM_DRP_START_NOM && !(&(~drp_done_reg2))) |=> fsm==FSM_DRP_START_NOM);

  // DRP_DONE_NOM
  assert property ((fsm==FSM_DRP_DONE_NOM && &drp_done_reg2) |=> fsm==FSM_QPLLLOCK);
  assert property ((fsm==FSM_DRP_DONE_NOM && !(&drp_done_reg2)) |=> fsm==FSM_DRP_DONE_NOM);

  // QPLLLOCK
  assert property ((fsm==FSM_QPLLLOCK && !(&qplllock_reg2)) |=> fsm==FSM_QPLLLOCK);
  assert property ((fsm==FSM_QPLLLOCK && &qplllock_reg2 && (BYPASS_COARSE_OVRD==1))  |=> fsm==FSM_QPLL_PDRESET);
  assert property ((fsm==FSM_QPLLLOCK && &qplllock_reg2 && (BYPASS_COARSE_OVRD==0))  |=> fsm==FSM_DRP_START_OPT);
  // Output in QPLLLOCK
  assert property ((fsm==FSM_QPLLLOCK) |-> qpllreset==1'b0);

  // DRP_START_OPT
  assert property ((fsm==FSM_DRP_START_OPT && &(~drp_done_reg2)) |=> fsm==FSM_DRP_DONE_OPT);
  assert property ((fsm==FSM_DRP_START_OPT && !(&(~drp_done_reg2))) |=> fsm==FSM_DRP_START_OPT);
  // ovrd asserted once OPT flow starts
  assert property ((fsm==FSM_DRP_START_OPT) |-> ovrd);

  // DRP_DONE_OPT
  assert property ((fsm==FSM_DRP_DONE_OPT && &drp_done_reg2 && (PCIE_PLL_SEL=="QPLL")) |=> fsm==FSM_QPLL_RESET);
  assert property ((fsm==FSM_DRP_DONE_OPT && &drp_done_reg2 && (PCIE_PLL_SEL!="QPLL")) |=> fsm==FSM_QPLL_PDRESET);
  assert property ((fsm==FSM_DRP_DONE_OPT && !(&drp_done_reg2)) |=> fsm==FSM_DRP_DONE_OPT);
  // qpllreset set when DONE_OPT completes and PLL_SEL==QPLL
  assert property ((fsm==FSM_DRP_DONE_OPT && &drp_done_reg2) |=> qpllreset == (PCIE_PLL_SEL=="QPLL"));

  // QPLL_RESET
  assert property ((fsm==FSM_QPLL_RESET && &(~qplllock_reg2)) |=> fsm==FSM_QPLLLOCK2);
  assert property ((fsm==FSM_QPLL_RESET && !(&(~qplllock_reg2))) |=> fsm==FSM_QPLL_RESET);
  assert property ((fsm==FSM_QPLL_RESET) |-> (qpllreset==1'b1 && qpllpd==1'b0));

  // QPLLLOCK2
  assert property ((fsm==FSM_QPLLLOCK2 && &qplllock_reg2) |=> fsm==FSM_IDLE);
  assert property ((fsm==FSM_QPLLLOCK2 && !(&qplllock_reg2)) |=> fsm==FSM_QPLLLOCK2);
  assert property ((fsm==FSM_QPLLLOCK2) |-> (qpllreset==1'b0 && qpllpd==1'b0));

  // QPLL_PDRESET -> QPLL_PD
  assert property ((fsm==FSM_QPLL_PDRESET) |=> fsm==FSM_QPLL_PD);
  assert property ((fsm==FSM_QPLL_PDRESET) |-> (qpllreset == ((PCIE_PLL_SEL=="CPLL") ? (rate_reg2!=2'd2) : 1'b0)));

  // QPLL_PD -> IDLE
  assert property ((fsm==FSM_QPLL_PD) |=> fsm==FSM_IDLE);
  assert property ((fsm==FSM_QPLL_PD) |-> (qpllpd == ((PCIE_PLL_SEL=="CPLL") ? (rate_reg2!=2'd2) : 1'b0)));

  // IDLE holds (absent reset)
  assert property ((fsm==FSM_IDLE) |=> fsm==FSM_IDLE);

  // Coverage: hit all states
  cover property (fsm==FSM_WAIT_LOCK);
  cover property (fsm==FSM_MMCM_LOCK);
  cover property (fsm==FSM_DRP_START_NOM);
  cover property (fsm==FSM_DRP_DONE_NOM);
  cover property (fsm==FSM_QPLLLOCK);
  cover property (fsm==FSM_DRP_START_OPT);
  cover property (fsm==FSM_DRP_DONE_OPT);
  cover property (fsm==FSM_QPLL_RESET);
  cover property (fsm==FSM_QPLLLOCK2);
  cover property (fsm==FSM_QPLL_PDRESET);
  cover property (fsm==FSM_QPLL_PD);
  cover property (fsm==FSM_IDLE);

  // Coverage: Nominal path to IDLE (BYPASS_COARSE_OVRD==1)
  generate if (BYPASS_COARSE_OVRD==1) begin
    cover property (
      fsm==FSM_WAIT_LOCK ##[1:$]
      fsm==FSM_MMCM_LOCK ##[1:$]
      fsm==FSM_DRP_START_NOM ##1
      fsm==FSM_DRP_DONE_NOM ##[1:$]
      fsm==FSM_QPLLLOCK ##[1:$]
      fsm==FSM_QPLL_PDRESET ##1
      fsm==FSM_QPLL_PD ##1
      fsm==FSM_IDLE
    );
  end endgenerate

  // Coverage: Optional DRP path (BYPASS_COARSE_OVRD==0) with both PLL_SEL branches
  generate if (BYPASS_COARSE_OVRD==0) begin
    // CPLL branch
    cover property (
      (PCIE_PLL_SEL!="QPLL") and
      (fsm==FSM_WAIT_LOCK) ##[1:$]
      fsm==FSM_MMCM_LOCK ##[1:$]
      fsm==FSM_DRP_START_NOM ##1
      fsm==FSM_DRP_DONE_NOM ##[1:$]
      fsm==FSM_QPLLLOCK ##[1:$]
      fsm==FSM_DRP_START_OPT ##1
      fsm==FSM_DRP_DONE_OPT ##[1:$]
      fsm==FSM_QPLL_PDRESET ##1
      fsm==FSM_QPLL_PD ##1
      fsm==FSM_IDLE
    );
    // QPLL branch
    cover property (
      (PCIE_PLL_SEL=="QPLL") and
      (fsm==FSM_WAIT_LOCK) ##[1:$]
      fsm==FSM_MMCM_LOCK ##[1:$]
      fsm==FSM_DRP_START_NOM ##1
      fsm==FSM_DRP_DONE_NOM ##[1:$]
      fsm==FSM_QPLLLOCK ##[1:$]
      fsm==FSM_DRP_START_OPT ##1
      fsm==FSM_DRP_DONE_OPT ##[1:$]
      fsm==FSM_QPLL_RESET ##[1:$]
      fsm==FSM_QPLLLOCK2 ##[1:$]
      fsm==FSM_IDLE
    );
  end endgenerate

  // Coverage: ovrd assertion event
  cover property ($rose(ovrd));

  // Coverage: IDLE pass-through observed
  cover property ((fsm==FSM_IDLE) && (&qpllreset_in_reg2) && (&qpllpd_in_reg2));

  // Coverage: CPLL power-save gating (rate!=2)
  generate if (PCIE_PLL_SEL=="CPLL") begin
    cover property ((fsm==FSM_QPLL_PDRESET) && (rate_reg2!=2'd2) && qpllreset);
    cover property ((fsm==FSM_QPLL_PD)      && (rate_reg2!=2'd2) && qpllpd);
  end endgenerate

endmodule

// Bind into DUT (example)
// bind pcie_7x_0_core_top_qpll_reset pcie_7x_0_core_top_qpll_reset_sva #(
//   .PCIE_PLL_SEL(PCIE_PLL_SEL),
//   .PCIE_POWER_SAVING(PCIE_POWER_SAVING),
//   .PCIE_LANE(PCIE_LANE),
//   .BYPASS_COARSE_OVRD(BYPASS_COARSE_OVRD)
// ) u_pcie_7x_0_core_top_qpll_reset_sva;