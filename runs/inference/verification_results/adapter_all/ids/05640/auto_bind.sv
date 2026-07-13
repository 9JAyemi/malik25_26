// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_i_read_en_const, assert, property, posedge, disable, iff, b1, check_i_addr_mapping, past, check_pc_hold_when_not_write, check_pc_load_when_write, check_pc_next_select_00, b00, check_pc_next_select_01, b01, check_pc_next_select_10, b10, check_pc_next_select_11, b11, check_if_id_next_i_addr_hold_when_not_write, check_if_id_next_i_addr_load_when_write, check_if_id_instruction_hold_when_not_write, check_if_id_instruction_zero_when_blocked, h00000000, check_if_id_instruction_load_when_write
bind if_stage if_stage_sva auto_sva_inst (
    .clk(clk),
    .rst(rst),
    .if_id_write_en(if_id_write_en),
    .pc_write(pc_write),
    .pc_source(pc_source),
    .pstop_i(pstop_i),
    .i_read_en(i_read_en),
    .i_addr(i_addr),
    .i_instr_in(i_instr_in),
    .jump_addr(jump_addr),
    .branch_addr(branch_addr),
    .reg_data_1(reg_data_1),
    .IF_ID_next_i_addr(IF_ID_next_i_addr),
    .IF_ID_instruction(IF_ID_instruction),
    .pc_reg(pc_reg),
    .b100011(b100011),
    .b101011(b101011),
    .pc_next(pc_next)
);
