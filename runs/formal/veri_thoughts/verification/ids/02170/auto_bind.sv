// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): CLK, check_index_a_priority, assert, property, posedge, h00, check_index_b_priority_when_a_zero, check_index_c_priority_when_a_b_zero, check_index_d_priority_when_a_b_c_zero, check_index_when_all_zero, decode_index_00_implies_a_nonzero, decode_index_01_implies_b_nonzero_and_a_zero, decode_index_10_implies_c_nonzero_and_a_b_zero, decode_index_11_implies_a_b_c_zero, mux_4to1_priority_encoder_sva, check_mux_sel_00_maps_to_a, check_mux_sel_01_maps_to_b, check_mux_sel_10_maps_to_c, check_mux_sel_11_maps_to_d
bind priority_encoder priority_encoder_sva auto_sva_inst (
    .a(a),
    .b(b),
    .c(c),
    .d(d),
    .index(index),
    .b00(b00),
    .b01(b01),
    .b10(b10),
    .b11(b11),
    .endmodule(endmodule),
    .module(module),
    .select(select),
    .out(out)
);
