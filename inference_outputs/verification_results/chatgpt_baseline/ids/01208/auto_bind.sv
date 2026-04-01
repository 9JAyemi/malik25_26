// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_sync_clears_outputs, assert, property, posedge, b0, b00, en_updates_control_o0, disable, iff, en_updates_control_o1, en_updates_control_o2, en_updates_pc_op_from_imm, b10, hold_when_en_low_control, past, hold_when_en_low_pc, hi_bits_unchanged_on_en, control_lowbits_change_only_with_en, changed, pc_op_changes_only_with_en, pc_op_valid_values, inside, pc_op_msb_matches_control2_on_update
bind control control_sva auto_sva_inst (
    .clk(clk),
    .rst(rst),
    .en(en),
    .en_mem(en_mem),
    .mem_wait(mem_wait),
    .should_branch(should_branch),
    .imm(imm),
    .control_o(control_o),
    .pc_op(pc_op)
);
