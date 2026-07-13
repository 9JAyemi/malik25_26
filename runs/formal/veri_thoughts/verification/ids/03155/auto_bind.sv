// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): typedef, u2_t, pipe_valid, b000, if, else, b1, function, automatic, add2, a, b, endfunction, mul2, check_s1_out_pipeline_function, assert, property, disable, iff, past, check_s2_out_pipeline_function, check_equal_delayed_inputs_give_equal_outputs, check_zero_delayed_inputs_force_zero_outputs, b00, check_zero_old_add_stage_removes_cross_paths, check_zero_direct_cos_term_removes_direct_paths
bind math_ops math_ops_assertions auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .cos(cos),
    .one(one),
    .s1(s1),
    .s2(s2),
    .s1_out(s1_out),
    .s2_out(s2_out),
    .always(always),
    .posedge(posedge),
    .begin(begin),
    .end(end)
);
