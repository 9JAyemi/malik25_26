// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_clears_ex, assert, property, posedge, b0, h0, b000, bubble_inserts_zeros, disable, iff, b1, propagate_instr_ops, past, propagate_operands, propagate_writeback, hold_on_full_stall, ex_change_has_valid_cause, zeros_persist_after_flush_then_hold
bind latch_id_ex latch_id_ex_sva auto_sva_inst (
    .clock(clock),
    .reset(reset),
    .stall(stall),
    .id_instruction(id_instruction),
    .ex_instruction(ex_instruction),
    .id_operator(id_operator),
    .ex_operator(ex_operator),
    .id_category(id_category),
    .ex_category(ex_category),
    .id_operand_a(id_operand_a),
    .ex_operand_a(ex_operand_a),
    .id_operand_b(id_operand_b),
    .ex_operand_b(ex_operand_b),
    .id_register_write_enable(id_register_write_enable),
    .ex_register_write_enable(ex_register_write_enable),
    .id_register_write_address(id_register_write_address),
    .ex_register_write_address(ex_register_write_address),
    .id_register_write_data(id_register_write_data),
    .ex_register_write_data(ex_register_write_data)
);
