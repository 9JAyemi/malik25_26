module IFID_Stage_sva (
    input logic clock,
    input logic reset,
    input logic IF_Flush,
    input logic IF_Stall,
    input logic ID_Stall,
    input logic [31:0] IF_Instruction,
    input logic [31:0] IF_PCAdd4,
    input logic [31:0] IF_PC,
    input logic IF_IsBDS,
    input logic [31:0] ID_Instruction,
    input logic [31:0] ID_PCAdd4,
    input logic [31:0] ID_RestartPC,
    input logic ID_IsBDS,
    input logic ID_IsFlushed,
    input logic [31:0] vote_ID_Instruction,
    input logic [31:0] vote_ID_PCAdd4,
    input logic [31:0] vote_ID_RestartPC,
    input logic vote_ID_IsBDS,
    input logic vote_ID_IsFlushed
);
    ///// Clocks/Resets /////
    // On reset, next cycle all vote_* outputs are cleared to 0.
    reset_clears_all: assert property (
        @(posedge clock) reset |-> ##1 (vote_ID_Instruction == 32'b0) && (vote_ID_PCAdd4 == 32'b0) && (vote_ID_RestartPC == 32'b0) && (vote_ID_IsBDS == 1'b0) && (vote_ID_IsFlushed == 1'b0)
    );

    ///// ID_Stall forwarding rules /////
    // With ID_Stall, next cycle vote_ID_Instruction comes from ID_Instruction.
    stall_forwards_instruction_from_ID: assert property (
        @(posedge clock) disable iff (reset) ID_Stall |-> ##1 (vote_ID_Instruction == $past(ID_Instruction))
    );
    // With ID_Stall, next cycle vote_ID_PCAdd4 comes from ID_PCAdd4.
    stall_forwards_pcadd4_from_ID: assert property (
        @(posedge clock) disable iff (reset) ID_Stall |-> ##1 (vote_ID_PCAdd4 == $past(ID_PCAdd4))
    );
    // With ID_Stall, next cycle vote_ID_IsBDS comes from ID_IsBDS.
    stall_forwards_isbds_from_ID: assert property (
        @(posedge clock) disable iff (reset) ID_Stall |-> ##1 (vote_ID_IsBDS == $past(ID_IsBDS))
    );
    // With ID_Stall, next cycle vote_ID_IsFlushed comes from ID_IsFlushed.
    stall_forwards_isflushed_from_ID: assert property (
        @(posedge clock) disable iff (reset) ID_Stall |-> ##1 (vote_ID_IsFlushed == $past(ID_IsFlushed))
    );
    // With ID_Stall, next cycle vote_ID_RestartPC comes from ID_RestartPC.
    stall_forwards_restartpc_from_ID: assert property (
        @(posedge clock) disable iff (reset) ID_Stall |-> ##1 (vote_ID_RestartPC == $past(ID_RestartPC))
    );

    ///// Non-stall datapath rules /////
    // Without ID_Stall and without IF_Stall/IF_Flush, next cycle instruction comes from IF_Instruction.
    nonstall_instruction_from_IF: assert property (
        @(posedge clock) disable iff (reset) (!ID_Stall && !(IF_Stall || IF_Flush)) |-> ##1 (vote_ID_Instruction == $past(IF_Instruction))
    );
    // Without ID_Stall and with IF_Stall or IF_Flush, next cycle instruction is zeroed.
    nonstall_instruction_zero_on_ifhold_or_flush: assert property (
        @(posedge clock) disable iff (reset) (!ID_Stall && (IF_Stall || IF_Flush)) |-> ##1 (vote_ID_Instruction == 32'b0)
    );
    // Without ID_Stall, next cycle PCAdd4 comes directly from IF_PCAdd4.
    nonstall_pcadd4_from_IF: assert property (
        @(posedge clock) disable iff (reset) (!ID_Stall) |-> ##1 (vote_ID_PCAdd4 == $past(IF_PCAdd4))
    );
    // Without ID_Stall, next cycle IsBDS comes directly from IF_IsBDS.
    nonstall_isbds_from_IF: assert property (
        @(posedge clock) disable iff (reset) (!ID_Stall) |-> ##1 (vote_ID_IsBDS == $past(IF_IsBDS))
    );
    // Without ID_Stall, next cycle IsFlushed comes directly from IF_Flush.
    nonstall_isflushed_from_IF: assert property (
        @(posedge clock) disable iff (reset) (!ID_Stall) |-> ##1 (vote_ID_IsFlushed == $past(IF_Flush))
    );

    ///// Restart PC selection /////
    // If IF_IsBDS, next cycle RestartPC comes from ID_RestartPC (regardless of stall).
    restartpc_from_ID_when_isbds: assert property (
        @(posedge clock) disable iff (reset) IF_IsBDS |-> ##1 (vote_ID_RestartPC == $past(ID_RestartPC))
    );
    // If not ID_Stall and not IF_IsBDS, next cycle RestartPC comes from IF_PC.
    restartpc_from_IF_pc_when_normal: assert property (
        @(posedge clock) disable iff (reset) (!ID_Stall && !IF_IsBDS) |-> ##1 (vote_ID_RestartPC == $past(IF_PC))
    );
endmodule