// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_i_read_en_tied_high, assert, property, posedge, disable, iff, b1, check_i_addr_div_by_four, past, initstate, b0, check_if_id_instruction_zero_on_reset, h00000000, check_if_id_next_i_addr_zero_on_reset, check_if_id_instruction_clears_when_disabled, check_if_id_next_i_addr_clears_when_disabled, check_if_id_instruction_captures_i_instr_in, check_if_id_next_i_addr_captures_next_i_addr, d4, check_pc_reg_zero_on_reset, check_pc_reg_holds_when_not_written, check_pc_reg_updates_on_write, b00, b01, b10
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
    .pc_reg(pc_reg)
);
