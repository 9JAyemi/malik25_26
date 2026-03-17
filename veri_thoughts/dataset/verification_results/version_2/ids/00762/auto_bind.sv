// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_clears_outputs, assert, property, posedge, b0, id_stall_captures_id_data, disable, iff, past, zero_if_fields_on_if_stall_or_flush, pass_if_fields_when_no_if_controls, restartpc_selects_id_on_flush_or_bds, restartpc_selects_if_on_normal_flow, flags_follow_id_isbds, b1, flags_follow_id_isflushed
bind pipeline_register pipeline_register_sva auto_sva_inst (
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
    .vote_ID_IsFlushed(vote_ID_IsFlushed)
);
