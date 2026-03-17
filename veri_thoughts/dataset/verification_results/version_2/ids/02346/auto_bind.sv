// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): clk, reset_n, OP_RTYPE, b000000, OP_LW, b100011, OP_SW, b101011, OP_BEQ, b000100, decode_rtype_match, assert, property, posedge, disable, iff, b0, b1, decode_lw_match, decode_sw_match, decode_beq_match, decode_default_zero, check_memread_write_mutex, unique_brnch_on_beq, unique_memoryread_on_lw, unique_memorywrite_on_sw, unique_memtoreg_on_rtype, unique_regdst_on_rtype, unique_aluop_on_rtype, unique_regw_on_rtype_or_lw, unique_alusrc_on_lw_or_sw
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
