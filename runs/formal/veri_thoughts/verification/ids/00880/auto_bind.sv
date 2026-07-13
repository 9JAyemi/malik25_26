// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_out_follows_xor_high, assert, property, b1, check_out_follows_xor_low, b0, pipeline_stage_1_sva, check_a_reg_high, check_a_reg_low, check_b_reg_high, check_b_reg_low, pipeline_stage_2_sva, check_out_reg_high, check_out_reg_low
bind pipelined_xor_gate pipelined_xor_gate_sva auto_sva_inst (
    .a(a),
    .b(b),
    .out_assign(out_assign),
    .clk(clk),
    .posedge(posedge),
    .endmodule(endmodule),
    .module(module),
    .a_reg(a_reg),
    .b_reg(b_reg),
    .xor_out(xor_out),
    .out_assign_reg(out_assign_reg)
);
