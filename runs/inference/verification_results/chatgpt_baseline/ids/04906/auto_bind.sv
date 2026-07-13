// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_q_matches_functional_out, assert, property, disable, iff, check_functional_out_reset_zero, check_q_reset_zero, check_counter_reset_zero, check_counter_increments, b1, past, d1, check_converter_positive_passthrough, check_converter_negative_formula, check_functional_out_selects_counter, check_functional_out_selects_converter, check_q_upper_nibble_zero
bind top_module top_module_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .signed_mag(signed_mag),
    .select(select),
    .q(q),
    .counter_out(counter_out),
    .converter_out(converter_out),
    .functional_out(functional_out),
    .posedge(posedge),
    .b0(b0)
);
