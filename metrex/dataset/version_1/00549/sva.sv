// SystemVerilog Assertions for NPCG_Toggle_BNC_P_program
// Bind into DUT; checks FSM, handshakes, outputs decode, sampling, and pass-through
// Concise, high-signal-to-noise

module NPCG_Toggle_BNC_P_program_sva;

  // Use DUT scope via bind (no ports). Access internal regs/locals directly.
  default clocking cb @(posedge iSystemClock); endclocking
  default disable iff (iReset);

  // Derived expressions
  wire w_trig_exp   = (iCMDValid && (iTargetID == 5'b00101) && (iOpcode == 6'b000100));
  wire any_pm_ready = |iPM_Ready;

  // -------------------------
  // Reset and state encoding
  // -------------------------
  // On reset cycle, state must be Idle (synchronous reset)
  assert property (@(posedge iSystemClock) iReset |-> (rCurState == State_Idle));

  // State encoding must be one of the defined states
  assert property (rCurState inside {
      State_Idle,State_NCALIssue0,State_NCmdWrite0,State_NAddrWrite0,State_NAddrWrite1,
      State_NAddrWrite2,State_NAddrWrite3,State_NAddrWrite4,State_WaitTADL,State_DOIssue,
      State_NCALIssue1,State_NCmdWrite1,State_NTimerIssue,State_WaitDone
  });

  // -------------------------
  // FSM next-state correctness
  // -------------------------
  // Idle
  assert property ((rCurState==State_Idle &&  w_trig_exp) |=> (rCurState==State_NCALIssue0));
  assert property ((rCurState==State_Idle && !w_trig_exp) |=> (rCurState==State_Idle));

  // NCALIssue0
  assert property ((rCurState==State_NCALIssue0 &&  any_pm_ready) |=> (rCurState==State_NCmdWrite0));
  assert property ((rCurState==State_NCALIssue0 && !any_pm_ready) |=> (rCurState==State_NCALIssue0));

  // Linear progress states
  assert property ((rCurState==State_NCmdWrite0)  |=> (rCurState==State_NAddrWrite0));
  assert property ((rCurState==State_NAddrWrite0) |=> (rCurState==State_NAddrWrite1));
  assert property ((rCurState==State_NAddrWrite1) |=> (rCurState==State_NAddrWrite2));
  assert property ((rCurState==State_NAddrWrite2) |=> (rCurState==State_NAddrWrite3));
  assert property ((rCurState==State_NAddrWrite3) |=> (rCurState==State_NAddrWrite4));
  assert property ((rCurState==State_NAddrWrite4) |=> (rCurState==State_WaitTADL));

  // WaitTADL
  assert property ((rCurState==State_WaitTADL &&  iPM_LastStep[3]) |=> (rCurState==State_DOIssue));
  assert property ((rCurState==State_WaitTADL && !iPM_LastStep[3]) |=> (rCurState==State_WaitTADL));

  // DOIssue
  assert property ((rCurState==State_DOIssue &&  iPM_LastStep[0]) |=> (rCurState==State_NCALIssue1));
  assert property ((rCurState==State_DOIssue && !iPM_LastStep[0]) |=> (rCurState==State_DOIssue));

  // NCALIssue1
  assert property ((rCurState==State_NCALIssue1 &&  iPM_LastStep[2]) |=> (rCurState==State_NCmdWrite1));
  assert property ((rCurState==State_NCALIssue1 && !iPM_LastStep[2]) |=> (rCurState==State_NCALIssue1));

  // NCmdWrite1 -> NTimerIssue
  assert property ((rCurState==State_NCmdWrite1) |=> (rCurState==State_NTimerIssue));

  // NTimerIssue
  assert property ((rCurState==State_NTimerIssue &&  iPM_LastStep[3]) |=> (rCurState==State_WaitDone));
  assert property ((rCurState==State_NTimerIssue && !iPM_LastStep[3]) |=> (rCurState==State_NTimerIssue));

  // WaitDone
  assert property ((rCurState==State_WaitDone &&  iPM_LastStep[0]) |=> (rCurState==State_Idle));
  assert property ((rCurState==State_WaitDone && !iPM_LastStep[0]) |=> (rCurState==State_WaitDone));

  // -------------------------
  // Start/Ready and LastStep
  // -------------------------
  // oStart is pure decode of trigger
  assert property (oStart == w_trig_exp);

  // oCMDReady only in Idle
  assert property (oCMDReady == (rCurState == State_Idle));

  // oLastStep iff WaitDone with iPM_LastStep[0]
  assert property (oLastStep |-> (rCurState==State_WaitDone && iPM_LastStep[0]));
  assert property ((rCurState==State_WaitDone && iPM_LastStep[0]) |-> oLastStep);

  // -------------------------
  // Sampling and stability of latched inputs
  // -------------------------
  // Capture on trigger in Idle (next cycle reflects $past inputs)
  assert property ((rCurState==State_Idle && w_trig_exp) |->
                   ##1 (rTargetWay==$past(iWaySelect)   &&
                        rColAddress==$past(iColAddress) &&
                        rRowAddress==$past(iRowAddress) &&
                        rTrfLength==$past(iLength)));

  // No re-sample when not Idle
  assert property ((rCurState!=State_Idle && w_trig_exp) |=> $stable({rTargetWay,rColAddress,rRowAddress,rTrfLength}));

  // Hold captured values until returning to Idle
  assert property (((rCurState==State_Idle && w_trig_exp) ##1 1'b1) |->
                   ($stable({rTargetWay,rColAddress,rRowAddress,rTrfLength}) until_with (rCurState==State_Idle)));

  // -------------------------
  // Output decode vs state
  // -------------------------
  // oPM_PCommand
  assert property (((rCurState==State_NCALIssue0)||(rCurState==State_NCALIssue1)) |-> (oPM_PCommand==8'h08));
  assert property ((rCurState==State_DOIssue)    |-> (oPM_PCommand==8'h04));
  assert property (((rCurState==State_WaitTADL)||(rCurState==State_NTimerIssue)) |-> (oPM_PCommand==8'h01));
  assert property ((rCurState inside {State_Idle,State_NCmdWrite0,State_NCmdWrite1,
                                      State_NAddrWrite0,State_NAddrWrite1,State_NAddrWrite2,
                                      State_NAddrWrite3,State_NAddrWrite4,State_WaitDone}) |-> (oPM_PCommand==8'h00));

  // oPM_PCommandOption
  assert property ((rCurState==State_DOIssue)    |-> (oPM_PCommandOption==3'b001));
  assert property ((rCurState==State_WaitTADL)   |-> (oPM_PCommandOption==3'b111));
  assert property ((rCurState==State_NTimerIssue)|-> (oPM_PCommandOption==3'b110));
  assert property ((rCurState inside {State_Idle,State_NCALIssue0,State_NCALIssue1,State_NCmdWrite0,State_NCmdWrite1,
                                      State_NAddrWrite0,State_NAddrWrite1,State_NAddrWrite2,
                                      State_NAddrWrite3,State_NAddrWrite4,State_WaitDone}) |-> (oPM_PCommandOption==3'b000));

  // oPM_NumOfData
  assert property ((rCurState==State_NCALIssue0) |-> (oPM_NumOfData==16'd5));
  assert property ((rCurState==State_DOIssue)    |-> (oPM_NumOfData==rTrfLength));
  assert property ((rCurState==State_NCALIssue1) |-> (oPM_NumOfData==16'd0));
  assert property ((rCurState==State_WaitTADL)   |-> (oPM_NumOfData==16'd31));
  assert property ((rCurState==State_NTimerIssue)|-> (oPM_NumOfData==16'd3));
  assert property ((rCurState inside {State_Idle,State_NCmdWrite0,State_NCmdWrite1,
                                      State_NAddrWrite0,State_NAddrWrite1,State_NAddrWrite2,
                                      State_NAddrWrite3,State_NAddrWrite4,State_WaitDone}) |-> (oPM_NumOfData==16'd0));

  // oPM_CASelect (command=0, address=1)
  assert property ((rCurState inside {State_NCmdWrite0,State_NCmdWrite1}) |-> (oPM_CASelect==1'b0));
  assert property ((rCurState inside {State_NAddrWrite0,State_NAddrWrite1,State_NAddrWrite2,State_NAddrWrite3,State_NAddrWrite4}) |-> (oPM_CASelect==1'b1));
  assert property ((rCurState inside {State_Idle,State_NCALIssue0,State_NCALIssue1,State_WaitTADL,State_DOIssue,State_NTimerIssue,State_WaitDone}) |-> (oPM_CASelect==1'b0));

  // oPM_CAData contents
  assert property ((rCurState==State_NCmdWrite0) |-> (oPM_CAData==8'h80));
  assert property ((rCurState==State_NAddrWrite0)|-> (oPM_CAData==rColAddress[7:0]));
  assert property ((rCurState==State_NAddrWrite1)|-> (oPM_CAData==rColAddress[15:8]));
  assert property ((rCurState==State_NAddrWrite2)|-> (oPM_CAData==rRowAddress[7:0]));
  assert property ((rCurState==State_NAddrWrite3)|-> (oPM_CAData==rRowAddress[15:8]));
  assert property ((rCurState==State_NAddrWrite4)|-> (oPM_CAData==rRowAddress[23:16]));
  assert property ((rCurState==State_NCmdWrite1) |-> (oPM_CAData==8'h10));
  assert property ((rCurState inside {State_Idle,State_NCALIssue0,State_NCALIssue1,State_WaitTADL,State_DOIssue,State_NTimerIssue,State_WaitDone}) |-> (oPM_CAData==8'h00));

  // oPM_TargetWay equals latched target way
  assert property (oPM_TargetWay == rTargetWay);

  // -------------------------
  // Write channel pass-through
  // -------------------------
  assert property (oPM_WriteData  == iWriteData);
  assert property (oPM_WriteValid == iWriteValid);
  assert property (oPM_WriteLast  == iWriteLast);
  assert property (oWriteReady    == iPM_WriteReady);

  // -------------------------
  // Functional coverage
  // -------------------------
  // Full happy-path transaction coverage
  cover property (
      (rCurState==State_Idle && w_trig_exp)
   ##1 (rCurState==State_NCALIssue0 && any_pm_ready)
   ##1 (rCurState==State_NCmdWrite0)
   ##1 (rCurState==State_NAddrWrite0)
   ##1 (rCurState==State_NAddrWrite1)
   ##1 (rCurState==State_NAddrWrite2)
   ##1 (rCurState==State_NAddrWrite3)
   ##1 (rCurState==State_NAddrWrite4)
   ##1 (rCurState==State_WaitTADL   && iPM_LastStep[3])
   ##1 (rCurState==State_DOIssue    && iPM_LastStep[0])
   ##1 (rCurState==State_NCALIssue1 && iPM_LastStep[2])
   ##1 (rCurState==State_NCmdWrite1)
   ##1 (rCurState==State_NTimerIssue && iPM_LastStep[3])
   ##1 (rCurState==State_WaitDone    && iPM_LastStep[0])
   ##1 (rCurState==State_Idle)
  );

  // Cover a start and corresponding lastStep pulse
  cover property ((oStart) ##[1:$] (oLastStep));

endmodule

bind NPCG_Toggle_BNC_P_program NPCG_Toggle_BNC_P_program_sva sva_npcg_toggle_bnc_p_program();