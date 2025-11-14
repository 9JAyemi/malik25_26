// SVA checker for pcieCore_qpll_reset
// Focuses on key FSM transitions, output mapping, parameter-dependent behavior, and basic coverage.
module pcieCore_qpll_reset_sva #(
  parameter string PCIE_PLL_SEL       = "CPLL",
  parameter string PCIE_POWER_SAVING  = "TRUE",
  parameter int    PCIE_LANE          = 1,
  parameter int    BYPASS_COARSE_OVRD = 1
)(
  input                           QRST_CLK,
  input                           QRST_RST_N,
  input                           QRST_MMCM_LOCK,
  input       [PCIE_LANE-1:0]     QRST_CPLLLOCK,
  input       [(PCIE_LANE-1)>>2:0]QRST_DRP_DONE,
  input       [(PCIE_LANE-1)>>2:0]QRST_QPLLLOCK,
  input       [ 1:0]              QRST_RATE,
  input       [PCIE_LANE-1:0]     QRST_QPLLRESET_IN,
  input       [PCIE_LANE-1:0]     QRST_QPLLPD_IN,
  output                          QRST_OVRD,
  output                          QRST_DRP_START,
  output                          QRST_QPLLRESET_OUT,
  output                          QRST_QPLLPD_OUT,
  output                          QRST_IDLE,
  output      [ 3:0]              QRST_FSM
);

  // FSM encodings mirrored from DUT
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
  default disable iff (!QRST_RST_N)

  // Basic reset behavior (synchronous)
  assert property (@cb !QRST_RST_N |-> (QRST_FSM == FSM_WAIT_LOCK && QRST_OVRD == 1'b0 && QRST_QPLLRESET_OUT == 1'b1 && QRST_QPLLPD_OUT == 1'b0));

  // Outputs map to states
  assert property (@cb (QRST_DRP_START === ((QRST_FSM==FSM_DRP_START_NOM) || (QRST_FSM==FSM_DRP_START_OPT))));
  assert property (@cb (QRST_IDLE === (QRST_FSM==FSM_IDLE)));

  // IDLE mapping of pass-through controls (accounting for 2-stage sync)
  assert property (@cb (QRST_FSM==FSM_IDLE) |-> (
      QRST_QPLLRESET_OUT == & $past(QRST_QPLLRESET_IN,2) &&
      ((PCIE_POWER_SAVING=="FALSE") ? (QRST_QPLLPD_OUT==1'b0) : (QRST_QPLLPD_OUT == & $past(QRST_QPLLPD_IN,2)))
  ));

  // QPLLLOCK state forces reset low
  assert property (@cb (QRST_FSM==FSM_QPLLLOCK) |-> (QRST_QPLLRESET_OUT==1'b0));

  // QPLL_RESET/QPLLLOCK2 state outputs
  assert property (@cb (QRST_FSM==FSM_QPLL_RESET)  |-> (QRST_QPLLRESET_OUT==1'b1 && QRST_QPLLPD_OUT==1'b0));
  assert property (@cb (QRST_FSM==FSM_QPLLLOCK2)   |-> (QRST_QPLLRESET_OUT==1'b0 && QRST_QPLLPD_OUT==1'b0));

  // DRP_START_OPT requires override
  assert property (@cb (QRST_FSM==FSM_DRP_START_OPT) |-> QRST_OVRD);

  // Power saving mask on QPLLPD_OUT
  if (PCIE_POWER_SAVING=="FALSE") begin
    assert property (@cb QRST_QPLLPD_OUT==1'b0);
  end

  // PLL-SEL dependent controls in PDRESET/PD (rate uses 2-cycle synced value)
  assert property (@cb (QRST_FSM==FSM_QPLL_PDRESET) |->
    (QRST_QPLLRESET_OUT == ((PCIE_PLL_SEL=="CPLL") ? ($past(QRST_RATE,2) != 2'd2) : 1'b0))
  );
  if (PCIE_POWER_SAVING=="TRUE") begin
    assert property (@cb (QRST_FSM==FSM_QPLL_PD) |->
      (QRST_QPLLPD_OUT == ((PCIE_PLL_SEL=="CPLL") ? ($past(QRST_RATE,2) != 2'd2) : 1'b0))
    );
  end

  // FSM value range
  assert property (@cb (QRST_FSM inside {[FSM_IDLE:FSM_QPLL_PD]}));

  // Output X checking (post-reset)
  assert property (@cb !$isunknown({QRST_OVRD, QRST_DRP_START, QRST_QPLLRESET_OUT, QRST_QPLLPD_OUT, QRST_IDLE, QRST_FSM}));

  // Next-state transition checks (all depend on 2-cycle synced inputs)
  assert property (@cb (QRST_FSM==FSM_WAIT_LOCK && (&(~$past(QRST_CPLLLOCK,2))) && (&(~$past(QRST_QPLLLOCK,2)))) |=> (QRST_FSM==FSM_MMCM_LOCK));
  assert property (@cb (QRST_FSM==FSM_MMCM_LOCK && ($past(QRST_MMCM_LOCK,2) && (&$past(QRST_CPLLLOCK,2)))) |=> (QRST_FSM==FSM_DRP_START_NOM));
  assert property (@cb (QRST_FSM==FSM_DRP_START_NOM && (&(~$past(QRST_DRP_DONE,2)))) |=> (QRST_FSM==FSM_DRP_DONE_NOM));
  assert property (@cb (QRST_FSM==FSM_DRP_DONE_NOM && (&$past(QRST_DRP_DONE,2))) |=> (QRST_FSM==FSM_QPLLLOCK));
  assert property (@cb (QRST_FSM==FSM_QPLLLOCK && (&$past(QRST_QPLLLOCK,2))) |=> (
    (BYPASS_COARSE_OVRD==1) ? (QRST_FSM==FSM_QPLL_PDRESET) : (QRST_FSM==FSM_DRP_START_OPT)
  ));
  assert property (@cb (QRST_FSM==FSM_DRP_START_OPT && (&(~$past(QRST_DRP_DONE,2)))) |=> (QRST_FSM==FSM_DRP_DONE_OPT));
  assert property (@cb (QRST_FSM==FSM_DRP_DONE_OPT && (&$past(QRST_DRP_DONE,2))) |=> (
    (PCIE_PLL_SEL=="QPLL") ? (QRST_FSM==FSM_QPLL_RESET) : (QRST_FSM==FSM_QPLL_PDRESET)
  ));
  assert property (@cb (QRST_FSM==FSM_QPLL_RESET  && (&(~$past(QRST_QPLLLOCK,2)))) |=> (QRST_FSM==FSM_QPLLLOCK2));
  assert property (@cb (QRST_FSM==FSM_QPLLLOCK2   && (&$past(QRST_QPLLLOCK,2)))  |=> (QRST_FSM==FSM_IDLE));
  assert property (@cb (QRST_FSM==FSM_QPLL_PDRESET) |=> (QRST_FSM==FSM_QPLL_PD));
  assert property (@cb (QRST_FSM==FSM_QPLL_PD)      |=> (QRST_FSM==FSM_IDLE));

  // Concise coverage
  cover property (@cb (QRST_FSM==FSM_IDLE));
  cover property (@cb (QRST_FSM==FSM_WAIT_LOCK ##1 QRST_FSM==FSM_MMCM_LOCK ##1 QRST_FSM==FSM_DRP_START_NOM
                       ##1 QRST_FSM==FSM_DRP_DONE_NOM ##1 QRST_FSM==FSM_QPLLLOCK));
  if (BYPASS_COARSE_OVRD!=1) begin
    cover property (@cb (QRST_FSM==FSM_QPLLLOCK && (&$past(QRST_QPLLLOCK,2))) ##1 (QRST_FSM==FSM_DRP_START_OPT)
                     ##1 (QRST_FSM==FSM_DRP_DONE_OPT)
                     ##1 ((PCIE_PLL_SEL=="QPLL") ? (QRST_FSM==FSM_QPLL_RESET) : (QRST_FSM==FSM_QPLL_PDRESET)));
  end
  if (BYPASS_COARSE_OVRD==1) begin
    cover property (@cb (QRST_FSM==FSM_QPLLLOCK && (&$past(QRST_QPLLLOCK,2))) ##1 (QRST_FSM==FSM_QPLL_PDRESET)
                     ##1 (QRST_FSM==FSM_QPLL_PD) ##1 (QRST_FSM==FSM_IDLE));
  end
  if (PCIE_POWER_SAVING=="TRUE" && PCIE_PLL_SEL=="CPLL") begin
    cover property (@cb (QRST_FSM==FSM_QPLL_PD && ($past(QRST_RATE,2)!=2'd2) && QRST_QPLLPD_OUT));
  end

endmodule

// Bind into DUT
bind pcieCore_qpll_reset
  pcieCore_qpll_reset_sva #(
    .PCIE_PLL_SEL(PCIE_PLL_SEL),
    .PCIE_POWER_SAVING(PCIE_POWER_SAVING),
    .PCIE_LANE(PCIE_LANE),
    .BYPASS_COARSE_OVRD(BYPASS_COARSE_OVRD)
  ) i_pcieCore_qpll_reset_sva (.*);