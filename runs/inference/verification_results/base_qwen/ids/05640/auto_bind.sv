// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): pc_update, assert, property, posedge, disable, iff, else, error, PC, register, update, mismatch, if_id_update, IF_ID, i_read_en_check, b1, should, always, be, i_addr_check, shifted, right, by, pc_source_00, b00, source, to, next, instruction, address, pc_source_01, b01, branch, pc_source_10, b10, jump, pc_source_11, b11, data, reset_behavior, Reset, drive, all, registers
bind if_stage if_stage_sva auto_sva_inst (
    .clk(clk),
    .rst(rst),
    .if_id_write_en(if_id_write_en),
    .pc_write(pc_write),
    .pc_source(pc_source),
    .pstop_i(pstop_i),
    .i_instr_in(i_instr_in),
    .jump_addr(jump_addr),
    .branch_addr(branch_addr),
    .reg_data_1(reg_data_1),
    .i_read_en(i_read_en),
    .i_addr(i_addr),
    .IF_ID_next_i_addr(IF_ID_next_i_addr),
    .IF_ID_instruction(IF_ID_instruction),
    .pc_reg(pc_reg),
    .pc_next(pc_next),
    .next_i_addr(next_i_addr)
);
