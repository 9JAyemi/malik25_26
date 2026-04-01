// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_outputs, assert, property, posedge, b0, b00, check_en_captures_en_mem, disable, iff, past, check_en_captures_should_branch, check_en_captures_imm, check_en_selects_and_when_imm, b10, check_en_selects_add_when_not_imm, check_hold_control_when_disabled, check_hold_pc_op_when_disabled
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
