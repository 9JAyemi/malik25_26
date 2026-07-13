// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_clears_all, assert, property, stall_forwards_instruction_from_ID, disable, iff, past, stall_forwards_pcadd4_from_ID, stall_forwards_isbds_from_ID, stall_forwards_isflushed_from_ID, stall_forwards_restartpc_from_ID, nonstall_instruction_from_IF, nonstall_instruction_zero_on_ifhold_or_flush, nonstall_pcadd4_from_IF, nonstall_isbds_from_IF, nonstall_isflushed_from_IF, restartpc_from_ID_when_isbds, restartpc_from_IF_pc_when_normal
bind IFID_Stage IFID_Stage_sva auto_sva_inst (
    .clock(clock),
    .reset(reset),
    .IF_Flush(IF_Flush),
    .IF_Stall(IF_Stall),
    .ID_Stall(ID_Stall),
    .IF_Instruction(IF_Instruction),
    .IF_PCAdd4(IF_PCAdd4),
    .IF_PC(IF_PC),
    .IF_IsBDS(IF_IsBDS),
    .ID_Instruction(ID_Instruction),
    .ID_PCAdd4(ID_PCAdd4),
    .ID_RestartPC(ID_RestartPC),
    .ID_IsBDS(ID_IsBDS),
    .ID_IsFlushed(ID_IsFlushed),
    .vote_ID_Instruction(vote_ID_Instruction),
    .vote_ID_PCAdd4(vote_ID_PCAdd4),
    .vote_ID_RestartPC(vote_ID_RestartPC),
    .vote_ID_IsBDS(vote_ID_IsBDS),
    .vote_ID_IsFlushed(vote_ID_IsFlushed),
    .posedge(posedge),
    .b0(b0)
);
