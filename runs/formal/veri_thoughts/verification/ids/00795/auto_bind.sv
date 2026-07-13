// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_out_is_xnor_of_inputs_next, assert, property, b1, check_equal_inputs_imply_out1_next, check_unequal_inputs_imply_out0_next, b0, check_xnor_alternative_expression_next, check_no_input_change_keeps_output_stable_next, stable, check_one_input_toggle_causes_output_toggle_next, onehot, changed, check_both_inputs_toggle_keeps_output_stable_next, check_a_toggle_only_causes_output_toggle_next, check_b_toggle_only_causes_output_toggle_next
bind xor_gate top_module_sva auto_sva_inst (
    .clk(clk),
    .a(a),
    .b(b),
    .out_always_ff(out_always_ff),
    .posedge(posedge)
);
