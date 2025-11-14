// SVA for NPCG_Toggle_BNC_P_read_DT00h
// Bind into the DUT with the single line at the bottom.

module NPCG_Toggle_BNC_P_read_DT00h_sva
#(parameter NumberOfWays = 4)
(
    input iSystemClock,
    input iReset,

    // DUT inputs/outputs we observe
    input  [5:0]  iOpcode,
    input  [4:0]  iTargetID,
    input  [4:0]  iSourceID,
    input  [15:0] iLength,
    input         iCMDValid,
    input         iReadReady,
    input  [NumberOfWays-1:0] iWaySelect,
    input  [15:0] iColAddress,
    input  [23:0] iRowAddress,
    input  [7:0]  iPM_Ready,
    input  [7:0]  iPM_LastStep,
    input  [31:0] iPM_ReadData,
    input         iPM_ReadLast,
    input         iPM_ReadValid,

    input         oCMDReady,
    input  [31:0] oReadData,
    input         oReadLast,
    input         oReadValid,
    input         oPM_ReadReady,
    input         oStart,
    input         oLastStep,
    input  [7:0]  oPM_PCommand,
    input  [2:0]  oPM_PCommandOption,
    input  [NumberOfWays-1:0] oPM_TargetWay,
    input  [15:0] oPM_NumOfData,
    input         oPM_CASelect,
    input  [7:0]  oPM_CAData,

    // Internal DUT symbols we rely on
    input  [3:0]  rCurState
);

    // State encodings (must match DUT)
    localparam State_Idle          = 4'b0000;
    localparam State_NPBRIssue     = 4'b0001;
    localparam State_NCmdIssue     = 4'b0011;
    localparam State_NCmdWrite0    = 4'b0010;
    localparam State_NCmdWrite1    = 4'b0110;
    localparam State_NCmdWrite2    = 4'b0111;
    localparam State_NCmdWrite3    = 4'b0101;
    localparam State_NTimer1Issue  = 4'b0100;
    localparam State_DIIssue       = 4'b1100;
    localparam State_NTimer2Issue  = 4'b1101;
    localparam State_WaitDone      = 4'b1111;

    // Derived expressions
    wire wModuleTriggered_exp = (iCMDValid && (iTargetID == 5'b00101) && (iOpcode == 6'b000011));
    wire pm_ready_nz = (iPM_Ready != 8'h00);

    default clocking cb @(posedge iSystemClock); endclocking
    default disable iff (iReset);

    // Basic equivalences
    assert property (oCMDReady == (rCurState == State_Idle));
    assert property (oStart    == wModuleTriggered_exp);

    // Read side passthrough
    assert property (oPM_ReadReady == iReadReady);
    assert property (oReadValid    == iPM_ReadValid);
    assert property (oReadLast     == iPM_ReadLast);
    assert property (oReadData     == iPM_ReadData);

    // Legal state encodings
    assert property (1'b1 |->
        rCurState inside {
            State_Idle, State_NPBRIssue, State_NCmdIssue,
            State_NCmdWrite0, State_NCmdWrite1, State_NCmdWrite2, State_NCmdWrite3,
            State_NTimer1Issue, State_DIIssue, State_NTimer2Issue, State_WaitDone
        }
    );

    // Next-state transitions
    // Idle
    assert property ((rCurState==State_Idle &&  wModuleTriggered_exp) |=> rCurState==State_NPBRIssue);
    assert property ((rCurState==State_Idle && !wModuleTriggered_exp) |=> rCurState==State_Idle);
    // NPBRIssue
    assert property ((rCurState==State_NPBRIssue &&  pm_ready_nz) |=> rCurState==State_NCmdIssue);
    assert property ((rCurState==State_NPBRIssue && !pm_ready_nz) |=> rCurState==State_NPBRIssue);
    // NCmdIssue
    assert property ((rCurState==State_NCmdIssue &&  iPM_LastStep[6]) |=> rCurState==State_NCmdWrite0);
    assert property ((rCurState==State_NCmdIssue && !iPM_LastStep[6]) |=> rCurState==State_NCmdIssue);
    // Write pipeline
    assert property ((rCurState==State_NCmdWrite0) |=> rCurState==State_NCmdWrite1);
    assert property ((rCurState==State_NCmdWrite1) |=> rCurState==State_NCmdWrite2);
    assert property ((rCurState==State_NCmdWrite2) |=> rCurState==State_NCmdWrite3);
    assert property ((rCurState==State_NCmdWrite3) |=> rCurState==State_NTimer1Issue);
    // Timer1
    assert property ((rCurState==State_NTimer1Issue &&  iPM_LastStep[3]) |=> rCurState==State_DIIssue);
    assert property ((rCurState==State_NTimer1Issue && !iPM_LastStep[3]) |=> rCurState==State_NTimer1Issue);
    // DI
    assert property ((rCurState==State_DIIssue &&  iPM_LastStep[0]) |=> rCurState==State_NTimer2Issue);
    assert property ((rCurState==State_DIIssue && !iPM_LastStep[0]) |=> rCurState==State_DIIssue);
    // Timer2
    assert property ((rCurState==State_NTimer2Issue &&  iPM_LastStep[1]) |=> rCurState==State_WaitDone);
    assert property ((rCurState==State_NTimer2Issue && !iPM_LastStep[1]) |=> rCurState==State_NTimer2Issue);
    // WaitDone and last step
    assert property (oLastStep == ((rCurState==State_WaitDone) && iPM_LastStep[0]));
    assert property ((rCurState==State_WaitDone &&  oLastStep) |=> rCurState==State_Idle);
    assert property ((rCurState==State_WaitDone && !oLastStep) |=> rCurState==State_WaitDone);

    // Command generation: oPM_PCommand
    assert property ((rCurState==State_NPBRIssue)     |-> oPM_PCommand==8'h40);
    assert property ((rCurState==State_NCmdIssue)     |-> oPM_PCommand==8'h08);
    assert property ((rCurState==State_NTimer1Issue)  |-> oPM_PCommand==8'h01);
    assert property ((rCurState==State_DIIssue)       |-> oPM_PCommand==8'h02);
    assert property ((rCurState==State_NTimer2Issue)  |-> oPM_PCommand==8'h01);
    assert property ((rCurState inside {State_Idle, State_NCmdWrite0, State_NCmdWrite1,
                                        State_NCmdWrite2, State_NCmdWrite3, State_WaitDone})
                     |-> oPM_PCommand==8'h00);

    // Command options
    assert property ((rCurState inside {State_NTimer1Issue, State_DIIssue}) |-> oPM_PCommandOption==3'b001);
    assert property ((rCurState==State_NTimer2Issue)                        |-> oPM_PCommandOption==3'b100);
    assert property ((rCurState inside {State_Idle, State_NPBRIssue, State_NCmdIssue,
                                        State_NCmdWrite0, State_NCmdWrite1, State_NCmdWrite2,
                                        State_NCmdWrite3, State_WaitDone})
                     |-> oPM_PCommandOption==3'b000);

    // NumOfData
    // Capture request length and way/addresses at trigger for later checks
    logic [15:0] cap_len;
    logic [NumberOfWays-1:0] cap_way;
    logic [15:0] cap_col;
    logic [23:0] cap_row;

    always_ff @(posedge iSystemClock) begin
        if (iReset) begin
            cap_len <= '0; cap_way <= '0; cap_col <= '0; cap_row <= '0;
        end else if (rCurState==State_Idle && wModuleTriggered_exp) begin
            cap_len <= iLength;
            cap_way <= iWaySelect;
            cap_col <= iColAddress;
            cap_row <= iRowAddress;
        end
    end

    assert property ((rCurState==State_NCmdIssue)    |-> oPM_NumOfData==16'd3);
    assert property ((rCurState==State_NTimer1Issue) |-> oPM_NumOfData==16'd33);
    assert property ((rCurState==State_DIIssue)      |-> oPM_NumOfData==cap_len);
    assert property ((rCurState==State_NTimer2Issue) |-> oPM_NumOfData==16'd3);
    assert property ((rCurState inside {State_Idle, State_NPBRIssue, State_NCmdWrite0, State_NCmdWrite1,
                                        State_NCmdWrite2, State_NCmdWrite3, State_WaitDone})
                     |-> oPM_NumOfData==16'd0);

    // Target way latch behavior
    assert property ((rCurState==State_Idle && wModuleTriggered_exp) |=> oPM_TargetWay==cap_way);
    assert property ($stable(oPM_TargetWay) throughout (! (rCurState==State_Idle && wModuleTriggered_exp)));

    // CA select/data on write cycles
    assert property ((rCurState==State_NCmdWrite0) |-> (oPM_CASelect==1'b0 && oPM_CAData==8'h05));
    assert property ((rCurState==State_NCmdWrite1) |-> (oPM_CASelect==1'b1 && oPM_CAData==cap_col[7:0]));
    assert property ((rCurState==State_NCmdWrite2) |-> (oPM_CASelect==1'b1 && oPM_CAData==cap_col[15:8]));
    assert property ((rCurState==State_NCmdWrite3) |-> (oPM_CASelect==1'b0 && oPM_CAData==8'hE0));
    assert property ((rCurState inside {State_Idle, State_NPBRIssue, State_NCmdIssue, State_NTimer1Issue,
                                        State_DIIssue, State_NTimer2Issue, State_WaitDone})
                     |-> (oPM_CASelect==1'b0 && oPM_CAData==8'h00));

    // Start/ready handshake coverage
    cover property (rCurState==State_Idle && wModuleTriggered_exp);

    // Full successful flow coverage (one transaction)
    cover property (
        rCurState==State_Idle && wModuleTriggered_exp
        ##1 rCurState==State_NPBRIssue
        ##[1:$] (pm_ready_nz && rCurState==State_NPBRIssue)
        ##1 rCurState==State_NCmdIssue
        ##[1:$] (iPM_LastStep[6] && rCurState==State_NCmdIssue)
        ##1 rCurState==State_NCmdWrite0 ##1 rCurState==State_NCmdWrite1
        ##1 rCurState==State_NCmdWrite2 ##1 rCurState==State_NCmdWrite3
        ##1 rCurState==State_NTimer1Issue
        ##[1:$] (iPM_LastStep[3] && rCurState==State_NTimer1Issue)
        ##1 rCurState==State_DIIssue
        ##[1:$] (iPM_LastStep[0] && rCurState==State_DIIssue)
        ##1 rCurState==State_NTimer2Issue
        ##[1:$] (iPM_LastStep[1] && rCurState==State_NTimer2Issue)
        ##1 rCurState==State_WaitDone
        ##[1:$] (oLastStep && rCurState==State_WaitDone)
        ##1 rCurState==State_Idle
    );

    // CA burst coverage
    cover property (
        rCurState==State_NCmdWrite0 && oPM_CAData==8'h05
        ##1 rCurState==State_NCmdWrite1 && oPM_CAData==cap_col[7:0]
        ##1 rCurState==State_NCmdWrite2 && oPM_CAData==cap_col[15:8]
        ##1 rCurState==State_NCmdWrite3 && oPM_CAData==8'hE0
    );

    // Read datapath coverage (valid+ready+last)
    cover property (oReadValid && oPM_ReadReady && oReadLast);

endmodule

// Bind into DUT (place in a package or a top-level include)
bind NPCG_Toggle_BNC_P_read_DT00h
     NPCG_Toggle_BNC_P_read_DT00h_sva #(.NumberOfWays(NumberOfWays)) npcg_toggle_bnc_p_read_dt00h_sva_i (.*);