// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): clk, OPC_LW, b100011, OPC_ADDI, b001000, OPC_BEQ, b000100, OPC_SW, b101011, OPC_BNE, b000101, OPC_RTYPE, b000000, OPC_J, b000010, check_lw_decode, assert, property, posedge, b0, b00, b1, check_addi_decode, check_beq_decode, b01, check_sw_decode, check_bne_decode, check_rtype_decode, b10, check_jump_decode, check_unlisted_opcode_defaults, check_branch_eq_only_beq, check_branch_ne_only_bne, check_memread_only_lw, check_memwrite_only_sw, check_jump_only_jump_opcode
bind control control_sva auto_sva_inst (
    .opcode(opcode),
    .branch_eq(branch_eq),
    .branch_ne(branch_ne),
    .aluop(aluop),
    .memread(memread),
    .memwrite(memwrite),
    .memtoreg(memtoreg),
    .regdst(regdst),
    .regwrite(regwrite),
    .alusrc(alusrc),
    .jump(jump)
);
