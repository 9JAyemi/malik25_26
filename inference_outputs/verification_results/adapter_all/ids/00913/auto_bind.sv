// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_ctrl_low_selects_adder, assert, property, posedge, disable, iff, check_ctrl_high_selects_comparator, b0000, check_comparator_encoding, check_equal_inputs_compare_result, check_greater_inputs_compare_result, check_less_inputs_compare_result, check_adder_zero_when_ctrl_high, check_adder_sum_when_ctrl_low, check_compare_onehot, onehot
bind top_module top_module_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .a(a),
    .b(b),
    .ctrl(ctrl),
    .out_adder(out_adder),
    .out_comparator(out_comparator),
    .b001(b001),
    .b100(b100),
    .b010(b010)
);
