// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): INSTR_RTYPE, b000000, INSTR_LW, b100011, INSTR_SW, b101011, INSTR_BEQ, b000100, INSTR_111111, b111111, INSTR_111110, b111110, decode_rtype, assert, property, posedge, b0100_100_010, decode_lw, b00_1111_0000, decode_111111, b00_1010_0000, decode_111110, b00_0000_0101, decode_sw_defined_bits, b1, b00, b0, decode_beq_defined_bits, b01, decode_default_others, invariant_saltoincond_zero, invariant_branch_flags, invariant_aluop01_means_branch, invariant_fuent_to_aluop, invariant_store_side_effects, invariant_load_side_effects, invariant_regwrite_no_branch_store, invariant_aluop10_rtype, b10
bind control control_sva auto_sva_inst (
    .clk(clk),
    .instru(instru),
    .RegDest(RegDest),
    .SaltoCond(SaltoCond),
    .LeerMem(LeerMem),
    .MemaReg(MemaReg),
    .ALUOp(ALUOp),
    .EscrMem(EscrMem),
    .FuenteALU(FuenteALU),
    .EscrReg(EscrReg),
    .Saltoincond(Saltoincond)
);
