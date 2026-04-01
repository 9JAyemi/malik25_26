// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_out_xor_function, assert, property, posedge, check_out_xor_inv_function, check_out_logical_inv_function, check_out_always_registered_function, b1, past, check_out_always_selects_logical_inv, check_out_always_selects_xor_inv, check_equal_outputs_imply_selected_equals_a, check_equal_xor_outputs_imply_selected_differs_a
bind xor_inv_multiplexer xor_inv_multiplexer_sva auto_sva_inst (
    .clk(clk),
    .a(a),
    .b(b),
    .sel_b1(sel_b1),
    .sel_b2(sel_b2),
    .sel_out(sel_out),
    .out_always(out_always),
    .out_xor(out_xor),
    .out_xor_inv(out_xor_inv),
    .out_logical_inv(out_logical_inv)
);
