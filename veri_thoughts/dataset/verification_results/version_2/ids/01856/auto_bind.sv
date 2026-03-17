// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): map_hi16_fields, assert, property, posedge, hi16_low_zero, h0000, zx16_upper_zero, reg3_matches_zx16_slice, sx16_low_matches_zx16_low, sx16_sign_extend_from_bit15, sx16s2_low_two_zero, b00, sx16s2_mid_matches_lowimm, sx16s2_sign_extend_from_bit15, sx26s2_low_two_zero, sx26s2_sign_extend_from_bit25, sx26s2_middle_matches_26imm, update_fields_on_ir_we, past, update_reg3_on_ir_we, update_zx16_on_ir_we, update_hi16_on_ir_we, update_sx16_on_ir_we, update_sx16s2_on_ir_we, update_sx26s2_on_ir_we
bind ir ir_sva auto_sva_inst (
    .clk(clk),
    .ir_we(ir_we),
    .instr(instr),
    .opcode(opcode),
    .reg1(reg1),
    .reg2(reg2),
    .reg3(reg3),
    .sx16(sx16),
    .zx16(zx16),
    .hi16(hi16),
    .sx16s2(sx16s2),
    .sx26s2(sx26s2)
);
