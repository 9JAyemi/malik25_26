// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_sum, assert, property, posedge, h00000000, check_select_low_adds_inputs, disable, iff, h00000000FFFFFFFF, check_select_high_subtracts_inputs, check_zero_b_passthrough, check_zero_a_inverts_b, check_equal_operands_cancel, check_stable_inputs_hold_sum, stable
bind adder_module top_module_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .a(a),
    .b(b),
    .select(select),
    .sum(sum)
);
