// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_outputs, assert, property, posedge, check_wb_capture_control, disable, iff, past, check_wb_capture_data, check_stall_flush_clear_control, check_stall_flush_clear_data, check_m_capture_control, check_m_capture_data
bind MEMWB_Stage MEMWB_Stage_sva auto_sva_inst (
    .clock(clock),
    .reset(reset),
    .M_Flush(M_Flush),
    .M_Stall(M_Stall),
    .WB_Stall(WB_Stall),
    .M_RegWrite(M_RegWrite),
    .M_MemtoReg(M_MemtoReg),
    .M_ReadData(M_ReadData),
    .M_ALU_Result(M_ALU_Result),
    .M_RtRd(M_RtRd),
    .WB_RegWrite(WB_RegWrite),
    .WB_MemtoReg(WB_MemtoReg),
    .WB_ReadData(WB_ReadData),
    .WB_ALU_Result(WB_ALU_Result),
    .WB_RtRd(WB_RtRd),
    .vote_WB_RegWrite(vote_WB_RegWrite),
    .vote_WB_MemtoReg(vote_WB_MemtoReg),
    .vote_WB_ReadData(vote_WB_ReadData),
    .vote_WB_ALU_Result(vote_WB_ALU_Result),
    .vote_WB_RtRd(vote_WB_RtRd),
    .b0(b0)
);
