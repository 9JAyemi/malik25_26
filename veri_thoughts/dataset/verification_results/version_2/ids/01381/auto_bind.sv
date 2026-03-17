// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): clk, reset_n, OPC_RTYPE, b000000, OPC_LW, b100011, OPC_SW, b101011, OPC_BEQ, b000100, check_decode_rtype, assert, property, posedge, disable, iff, b0, b1, check_decode_lw, check_decode_sw, check_decode_beq, check_decode_default, check_rd_wr_mutex, check_aluop_only_rtype, check_regdst_only_rtype, check_memtoreg_only_rtype, check_alusrc_lw_or_sw, check_regw_rtype_or_lw, check_memoryread_implies_lw, check_memorywrite_implies_sw, check_branch_implies_beq_no_mem, check_memtoreg_implies_regw, check_stability_when_input_stable, past
bind controlunit controlunit_sva auto_sva_inst (
    .imemout(imemout),
    .brnch(brnch),
    .memorywrite(memorywrite),
    .memoryread(memoryread),
    .alusrc(alusrc),
    .regw(regw),
    .regdst(regdst),
    .aluop(aluop),
    .memtoreg(memtoreg)
);
