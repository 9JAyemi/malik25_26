// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): clk, check_jmp_decode, assert, property, posedge, b000010, check_regdst_decode, b000000, check_memtoreg_decode, b100011, check_memwrite_decode, b101011, check_branch_decode, b000100, check_aluop1_decode, check_aluop0_decode, check_writereg_decode, check_alusrcb_decode, check_aluop1_matches_regdst, check_aluop0_matches_branch, check_writereg_relation, check_alusrcb_relation
bind cpu_ctr cpu_ctr_sva auto_sva_inst (
    .opcode(opcode),
    .RegDst(RegDst),
    .ALUsrcB(ALUsrcB),
    .MemToReg(MemToReg),
    .WriteReg(writeReg),
    .MemWrite(MemWrite),
    .Branch(Branch),
    .ALUop1(ALUop1),
    .ALUop0(ALUop0),
    .JMP(JMP)
);
