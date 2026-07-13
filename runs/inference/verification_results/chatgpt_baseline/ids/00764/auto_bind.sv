// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_out_xor_from_mux, assert, property, posedge, check_out_xor_inv_is_not, check_out_logical_inv_is_nor, check_sel_b2_drives_b_xor_a, check_sel_b1_drives_when_b2_low, check_both_selects_zero_xor_zero, b0000, check_both_selects_zero_inv_ones, b1111, check_xor_zero_implies_logical_inv_one, b1, check_out_always_follows_prev_xor_inv_sel0, past, b0, check_out_always_follows_prev_logical_inv_sel1
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
