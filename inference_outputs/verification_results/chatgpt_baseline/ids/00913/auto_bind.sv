// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_mux_ctrl0_out_adder_sum, assert, property, posedge, disable, iff, check_mux_ctrl0_out_comp_sum_low3, check_mux_ctrl1_out_adder_comp_packed, b0, check_mux_ctrl1_out_comp_code, check_low3_consistency, check_msb_zero_when_ctrl1, check_msb_matches_sum_when_ctrl0, check_out_adder_matches_ctrl_based_spec, check_comp_onehot_when_ctrl1, onehot
bind top_module top_module_assertions auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .a(a),
    .b(b),
    .ctrl(ctrl),
    .out_adder(out_adder),
    .out_comparator(out_comparator),
    .b100(b100),
    .b010(b010),
    .b001(b001)
);
