// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_clears_sum_next, assert, property, past, h00, reset_clears_product_next, reset_clears_difference_next, adder_updates_from_inputs_onecycle, disable, iff, multiplier_updates_from_inputs_low8_onecycle, difference_updates_from_regs_onecycle, difference_two_cycle_from_primary_inputs, adder_stable_when_inputs_hold, multiplier_stable_when_inputs_hold, difference_stable_when_prev_regs_hold, difference_linear_relation_prev_cycle
bind top_module top_module_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .a(a),
    .b(b),
    .sum_output(sum_output),
    .product_output(product_output),
    .difference_output(difference_output),
    .posedge(posedge)
);
