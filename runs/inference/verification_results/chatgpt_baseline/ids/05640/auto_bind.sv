// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_state, assert, property, posedge, d0, check_read_enable_high, disable, iff, b1, check_i_addr_upper_bits_zero, b00, check_pc_holds_without_enabled_update, past, check_pc_uses_sequential_next_addr, d1, check_pc_uses_branch_addr, b01, check_pc_uses_jump_addr, b10, check_pc_uses_reg_data_1, b11, check_ifid_holds_without_write_enable, check_ifid_captures_next_addr_upper_bits, check_ifid_captures_instruction_when_not_stopped, check_ifid_zeros_instruction_when_stopped
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
    .mem_op(mem_op),
    .b100011(b100011),
    .b101011(b101011)
);
