// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_clears_outputs, assert, property, posedge, b0, b00, hold_when_en_low, disable, iff, past, control0_captures_en_mem, control1_captures_should_branch, control2_captures_imm, pc_op_captures_10_on_imm, b10, pc_op_captures_00_on_no_imm, pc_op_legal_values_when_en, pc_op_change_requires_prev_en, changed, control_o_change_requires_prev_en
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
