// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_outputs, assert, property, posedge, d0, b0, check_capture_alu_result, disable, iff, past, check_capture_r_data2, check_capture_mux_regdst, check_capture_wb_regwrite, check_capture_wb_memtoreg, check_capture_m_memwrite, check_capture_opcode, check_hold_when_disabled, stable, check_output_change_requires_prev_update, initstate, changed
bind latch_EX_MEM latch_EX_MEM_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .ena(ena),
    .alu_result_in(alu_result_in),
    .r_data2_in(r_data2_in),
    .mux_RegDst_in(mux_RegDst_in),
    .wb_RegWrite_in(wb_RegWrite_in),
    .wb_MemtoReg_in(wb_MemtoReg_in),
    .m_MemWrite_in(m_MemWrite_in),
    .opcode_in(opcode_in),
    .alu_result_out(alu_result_out),
    .r_data2_out(r_data2_out),
    .mux_RegDst_out(mux_RegDst_out),
    .wb_RegWrite_out(wb_RegWrite_out),
    .wb_MemtoReg_out(wb_MemtoReg_out),
    .m_MemWrite_out(m_MemWrite_out),
    .opcode_out(opcode_out)
);
