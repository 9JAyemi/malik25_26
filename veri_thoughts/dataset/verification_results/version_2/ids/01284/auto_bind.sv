// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): CLK, RESETn, check_stall_fetch_const_zero, assert, property, posedge, disable, iff, b0, check_stall_iss_const_zero, check_flush_ex_definition, check_flush_iss_definition, check_flush_ex_implies_taken_mispred, check_flush_ex_implies_flush_iss, check_jump_sets_flush_iss, check_fwd_p1_memwb_select, b10, check_fwd_p1_wbret_select, b01, check_fwd_p1_default_zero, b00, check_fwd_p1_when_10_implies_memwb, check_fwd_p1_when_01_implies_wbret, check_fwd_p1_when_00_implies_none, check_fwd_p1_never_11, inside, check_fwd_p2_memwb_select, check_fwd_p2_wbret_select, check_fwd_p2_default_zero, check_fwd_p2_when_10_implies_memwb, check_fwd_p2_when_01_implies_wbret, check_fwd_p2_when_00_implies_none, check_fwd_p2_never_11
bind hazard_unit hazard_unit_sva auto_sva_inst (
    .rs_ex_mem_hz_i(rs_ex_mem_hz_i),
    .rt_ex_mem_hz_i(rt_ex_mem_hz_i),
    .rd_mem_wb_hz_i(rd_mem_wb_hz_i),
    .rd_wb_ret_hz_i(rd_wb_ret_hz_i),
    .mem_to_reg_ex_mem_hz_i(mem_to_reg_ex_mem_hz_i),
    .reg_wr_mem_wb_hz_i(reg_wr_mem_wb_hz_i),
    .reg_wr_wb_ret_hz_i(reg_wr_wb_ret_hz_i),
    .branch_taken_ex_mem_hz_i(branch_taken_ex_mem_hz_i),
    .jump_iss_ex_hz_i(jump_iss_ex_hz_i),
    .brn_pred_ex_mem_hz_i(brn_pred_ex_mem_hz_i),
    .stall_fetch_hz_o(stall_fetch_hz_o),
    .stall_iss_hz_o(stall_iss_hz_o),
    .flush_ex_hz_o(flush_ex_hz_o),
    .flush_iss_hz_o(flush_iss_hz_o),
    .fwd_p1_ex_mem_hz_o(fwd_p1_ex_mem_hz_o),
    .fwd_p2_ex_mem_hz_o(fwd_p2_ex_mem_hz_o)
);
