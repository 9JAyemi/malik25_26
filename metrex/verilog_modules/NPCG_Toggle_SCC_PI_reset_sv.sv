// SVA for NPCG_Toggle_SCC_PI_reset
// Includes a pure-I/O SVA module and an optional internal SVA module.
// Example bind lines are at the end.

// I/O-only SVA module (black-box friendly)
module NPCG_Toggle_SCC_PI_reset_sva
#(parameter int NumberOfWays = 4)
(
    input  logic         iSystemClock,
    input  logic         iReset,
    input  logic [5:0]   iOpcode,
    input  logic [4:0]   iTargetID,
    input  logic [4:0]   iSourceID,
    input  logic         iCMDValid,
    input  logic         oCMDReady,
    input  logic         oStart,
    input  logic         oLastStep,
    input  logic [7:0]   iPM_Ready,
    input  logic [7:0]   iPM_LastStep,
    input  logic [7:0]   oPM_PCommand
);

    default clocking cb @(posedge iSystemClock); endclocking
    default disable iff (iReset);

    localparam logic [5:0] OPCODE  = 6'b110010;
    localparam logic [4:0] TGT_ID  = 5'b00101;

    // Recreate trigger and state from I/O observables
    logic wModuleTriggered_sva;
    assign wModuleTriggered_sva = iCMDValid && (iTargetID == TGT_ID) && (iOpcode == OPCODE);

    logic idle_s, issue_s, wait_s;
    assign idle_s  = oCMDReady;           // Idle is directly observable
    assign issue_s = oPM_PCommand[4];     // PIResetIssue is directly observable
    assign wait_s  = !idle_s && !issue_s; // Remaining state (PIWait) from outputs

    // Basic decodes and output mapping
    assert property (oStart == wModuleTriggered_sva)
      else $error("oStart must equal trigger condition (iCMDValid && iTargetID==5'b00101 && iOpcode==6'b110010)");

    assert property (oPM_PCommand == (issue_s ? 8'h10 : 8'h00))
      else $error("oPM_PCommand encoding must be 8'h10 in PIResetIssue, else 8'h00");

    assert property (oLastStep == (wait_s & iPM_LastStep[4]))
      else $error("oLastStep must assert only in PIWait when iPM_LastStep[4]==1; deassert otherwise");

    // State coherence checks
    assert property (!(idle_s && issue_s))
      else $error("Illegal overlap: Idle and PIResetIssue cannot both be true");

    // After reset rises, DUT must be in Idle next cycle (no disable on this check)
    assert property (@(posedge iSystemClock) disable iff (1'b0) $rose(iReset) |=> oCMDReady)
      else $error("Post-reset, DUT must be Idle (oCMDReady==1) on the next cycle");

    // Idle state transitions
    assert property (idle_s && !wModuleTriggered_sva |=> idle_s)
      else $error("Idle must hold when no trigger");

    assert property (idle_s && wModuleTriggered_sva |=> issue_s)
      else $error("Idle + trigger must transition to PIResetIssue on next clock");

    // PIResetIssue transitions (advance when any iPM_Ready bit is 1)
    assert property (issue_s && (iPM_Ready == 8'h00) |=> issue_s)
      else $error("PIResetIssue must hold while iPM_Ready==0");

    assert property (issue_s && (iPM_Ready != 8'h00) |=> wait_s)
      else $error("PIResetIssue must transition to PIWait when any iPM_Ready bit is 1");

    // PIWait transitions (wait for iPM_LastStep[4])
    assert property (wait_s && !iPM_LastStep[4] |=> wait_s && !oLastStep)
      else $error("PIWait must hold while iPM_LastStep[4]==0 and oLastStep must be 0");

    assert property (wait_s && iPM_LastStep[4] |-> oLastStep && ##1 idle_s)
      else $error("PIWait + iPM_LastStep[4]==1 must assert oLastStep and return to Idle on next cycle");

    // Output encoding safety
    assert property (!issue_s |-> oPM_PCommand == 8'h00)
      else $error("oPM_PCommand must be zeroed outside PIResetIssue");
    assert property (issue_s  |-> oPM_PCommand == 8'h10)
      else $error("oPM_PCommand must be 8'h10 in PIResetIssue");
    assert property (oPM_PCommand[7:5] == 3'b000 && oPM_PCommand[3:0] == 4'b0000)
      else $error("oPM_PCommand reserved bits must be 0");

    // oCMDReady must be deasserted outside Idle
    assert property (!idle_s |-> !oCMDReady)
      else $error("oCMDReady must be 0 outside Idle");

    // Coverage: hit states, transitions, stalls, and key outputs
    cover property (idle_s);
    cover property (issue_s);
    cover property (wait_s);

    // Full happy-path sequence: Idle -> trigger -> Issue -> Ready -> Wait -> LastStep -> Idle
    cover property (
        idle_s
        ##1 (idle_s && wModuleTriggered_sva)
        ##1 issue_s
        ##[1:$] (issue_s && (iPM_Ready != 8'h00))
        ##1 wait_s
        ##[1:$] (wait_s && !iPM_LastStep[4])
        ##1 (wait_s && iPM_LastStep[4] && oLastStep)
        ##1 idle_s
    );

    // Stalls in intermediate states
    cover property (issue_s ##1 issue_s); // stayed at least 1 extra cycle in Issue
    cover property (wait_s  ##1 wait_s);  // stayed at least 1 extra cycle in Wait

    // Observe starts and commands in various situations
    cover property (oStart && idle_s);
    cover property (oStart && !idle_s);
    cover property (oPM_PCommand == 8'h10);
    cover property (oLastStep);

endmodule


// Optional internal SVA module using internal DUT signals for stronger checks.
// Bind this only if you can connect to internals.
module NPCG_Toggle_SCC_PI_reset_internal_sva
(
    input  logic         iSystemClock,
    input  logic         iReset,
    input  logic [2:0]   rCurState,       // internal
    input  logic [7:0]   iPM_Ready,
    input  logic [7:0]   iPM_LastStep,
    input  logic         wModuleTriggered,// internal
    input  logic         wPIResetTrig     // internal
);
    default clocking cb @(posedge iSystemClock); endclocking
    default disable iff (iReset);

    localparam logic [2:0] State_Idle         = 3'b000;
    localparam logic [2:0] State_PIResetIssue = 3'b001;
    localparam logic [2:0] State_PIWait       = 3'b011;

    // FSM state legality
    assert property (rCurState inside {State_Idle, State_PIResetIssue, State_PIWait})
      else $error("Illegal FSM state: %b", rCurState);

    // Internal equivalences
    assert property (wPIResetTrig == (rCurState == State_PIResetIssue))
      else $error("wPIResetTrig must be 1 only in State_PIResetIssue");

    // Next-state function checks (re-state the RTL)
    assert property ((rCurState == State_Idle) &&  wModuleTriggered |=> rCurState == State_PIResetIssue)
      else $error("FSM: Idle + trigger must go to PIResetIssue");
    assert property ((rCurState == State_Idle) && !wModuleTriggered |=> rCurState == State_Idle)
      else $error("FSM: Idle must hold without trigger");

    assert property ((rCurState == State_PIResetIssue) && (iPM_Ready == 8'h00) |=> rCurState == State_PIResetIssue)
      else $error("FSM: PIResetIssue must hold while iPM_Ready==0");
    assert property ((rCurState == State_PIResetIssue) && (iPM_Ready != 8'h00) |=> rCurState == State_PIWait)
      else $error("FSM: PIResetIssue must go to PIWait when any iPM_Ready bit is 1");

    assert property ((rCurState == State_PIWait) && !iPM_LastStep[4] |=> rCurState == State_PIWait)
      else $error("FSM: PIWait must hold while iPM_LastStep[4]==0");
    assert property ((rCurState == State_PIWait) &&  iPM_LastStep[4] |=> rCurState == State_Idle)
      else $error("FSM: PIWait + iPM_LastStep[4]==1 must go to Idle next cycle");

    // Coverage: each state and transitions (internal view)
    cover property (rCurState == State_Idle);
    cover property (rCurState == State_PIResetIssue);
    cover property (rCurState == State_PIWait);

    cover property ((rCurState == State_Idle)         ##1 (rCurState == State_PIResetIssue));
    cover property ((rCurState == State_PIResetIssue) ##1 (rCurState == State_PIWait));
    cover property ((rCurState == State_PIWait)       ##1 (rCurState == State_Idle));
endmodule


// Example bind (put in your testbench or a bind file):
// bind NPCG_Toggle_SCC_PI_reset NPCG_Toggle_SCC_PI_reset_sva #(.NumberOfWays(NumberOfWays)) sva_io (.*);

// Optional internal bind if your simulator allows hierarchical connects:
// bind NPCG_Toggle_SCC_PI_reset NPCG_Toggle_SCC_PI_reset_internal_sva sva_int (
//     .iSystemClock(iSystemClock),
//     .iReset(iReset),
//     .rCurState(rCurState),
//     .iPM_Ready(iPM_Ready),
//     .iPM_LastStep(iPM_LastStep),
//     .wModuleTriggered(wModuleTriggered),
//     .wPIResetTrig(wPIResetTrig)
// );