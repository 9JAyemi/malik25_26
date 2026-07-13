// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_outputs, assert, property, posedge, b0, b00, check_control_en_mem_capture, disable, iff, past, check_control_branch_capture, check_control_imm_capture, check_pc_op_and_when_imm_high, b10, check_pc_op_add_when_imm_low, check_control_hold_when_disabled, check_pc_op_hold_when_disabled
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
