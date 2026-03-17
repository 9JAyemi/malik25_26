// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): decode_rtype, assert, property, posedge, past, b000000, b1, b0, b10, decode_lw, b100011, b00, decode_sw, b101011, decode_beq, b000100, b01, decode_addi, b001000, decode_jump, b000010, decode_default_other, check_mem_rw_mutex, isunknown, check_mem_to_reg_eq_mem_read, check_alu_op_range, b11
bind Control Control_sva auto_sva_inst (
    .opcode(opcode),
    .clk(clk),
    .reg_dst(reg_dst),
    .jump(jump),
    .branch(branch),
    .ctrl_mem_read(ctrl_mem_read),
    .mem_to_reg(mem_to_reg),
    .ctrl_mem_write(ctrl_mem_write),
    .alu_src(alu_src),
    .reg_write(reg_write),
    .alu_op(alu_op)
);
