// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): CLK, RESETn, check_regDst_equals_aluop1, assert, property, posedge, disable, iff, check_branch_equals_aluop0, check_memToReg_equals_memRead, check_aluSrc_equals_memRead_or_memWrite, check_regWrite_equals_memToReg_or_regDst, check_aluop_mutex, check_mem_mutex, check_memToReg_implies_regWrite, check_regDst_implies_regWrite, check_memWrite_implies_no_regWrite, check_decode_op_000000, b000000, b10, b1, b0, check_decode_op_000100, b000100, b01, check_decode_op_100011, b100011, b00, check_decode_op_101011, b101011
bind control control_sva auto_sva_inst (
    .op(op),
    .alu_op(alu_op),
    .regDst(regDst),
    .aluSrc(aluSrc),
    .memToReg(memToReg),
    .regWrite(regWrite),
    .memRead(memRead),
    .memWrite(memWrite),
    .branch(branch)
);
