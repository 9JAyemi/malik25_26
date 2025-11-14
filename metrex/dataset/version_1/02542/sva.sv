// SVA for NPCG_Toggle_SCC_PI_reset
// Bind into DUT; references internal signals directly inside bound scope.

module NPCG_Toggle_SCC_PI_reset_sva;

  // Mirror DUT encodings
  localparam  State_Idle          = 3'b000;
  localparam  State_PIResetIssue  = 3'b001;
  localparam  State_PIWait        = 3'b011;

  // Trigger helper
  function automatic bit trig();
    return iCMDValid && (iTargetID == 5'b00101) && (iOpcode == 6'b110010);
  endfunction

  default clocking cb @(posedge iSystemClock); endclocking
  default disable iff (iReset);

  // Reset behavior
  a_reset_to_idle:        assert property ($rose(iReset) |=> rCurState == State_Idle);

  // State encoding sanity
  a_state_in_set:         assert property (rCurState inside {State_Idle, State_PIResetIssue, State_PIWait});

  // FSM transitions
  a_idle_hold:            assert property ((rCurState == State_Idle && !trig()) |=> rCurState == State_Idle);
  a_idle_to_issue:        assert property ((rCurState == State_Idle &&  trig()) |=> rCurState == State_PIResetIssue);

  a_issue_hold:           assert property ((rCurState == State_PIResetIssue && !iPM_Ready) |=> rCurState == State_PIResetIssue);
  a_issue_to_wait:        assert property ((rCurState == State_PIResetIssue &&  iPM_Ready) |=> rCurState == State_PIWait);

  a_wait_hold:            assert property ((rCurState == State_PIWait && !oLastStep) |=> rCurState == State_PIWait);
  a_wait_to_idle:         assert property ((rCurState == State_PIWait &&  oLastStep) |=> rCurState == State_Idle);

  // Internal wire correctness
  a_wModuleTriggered:     assert property (wModuleTriggered == trig());
  a_wPIResetTrig:         assert property (wPIResetTrig == (rCurState == State_PIResetIssue));

  // Output equivalences
  a_cmdready_eq_state:    assert property (oCMDReady == (rCurState == State_Idle));
  a_start_eq_trigger:     assert property (oStart == trig());
  a_laststep_eq_logic:    assert property (oLastStep == ((rCurState == State_PIWait) && iPM_LastStep[4]));

  a_pm_cmd_map:           assert property (oPM_PCommand == (rCurState == State_PIResetIssue ? 8'h10 : 8'h00));

  // Key coverage
  c_full_flow:            cover property (
                            (rCurState == State_Idle && trig())
                            ##1 (rCurState == State_PIResetIssue)
                            ##[1:$] iPM_Ready
                            ##1 (rCurState == State_PIWait)
                            ##[1:$] iPM_LastStep[4]
                            ##1 (rCurState == State_Idle)
                          );

  c_pulse_cmd_bit4:       cover property (oPM_PCommand == 8'h10);
  c_laststep_obs:         cover property (oLastStep);

  c_back_to_back:         cover property (
                            (rCurState == State_Idle && trig())
                            ##1 (rCurState == State_PIResetIssue)
                            ##[1:$] iPM_Ready
                            ##1 (rCurState == State_PIWait)
                            ##[1:$] iPM_LastStep[4]
                            ##1 (rCurState == State_Idle)
                            ##[1:10] trig()
                          );

endmodule

bind NPCG_Toggle_SCC_PI_reset NPCG_Toggle_SCC_PI_reset_sva svachk();