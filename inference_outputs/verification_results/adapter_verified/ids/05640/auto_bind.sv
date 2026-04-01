// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_i_read_en_high, assert, property, posedge, disable, iff, b1, check_i_addr_div_by_4, check_next_i_addr_capture, check_instruction_capture, next_instruction, check_next_i_addr_write_enable, check_instruction_write_enable, if_id_write_enable, check_next_i_addr_hold, past, check_instruction_hold, check_instruction_load_data, check_instruction_clear_on_stop_or_memop, h0, check_next_i_addr_load_on_write, check_next_i_addr_clear_on_stop_or_memop
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
    .next_i_addr(next_i_addr),
    .mem_op(mem_op)
);
