// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_register_clears_on_reset, assert, property, h00, check_counter_clears_on_reset, h0, check_outputs_clear_on_reset, check_register_captures_d, disable, iff, b1, past, check_counter_increments, d1, check_mux_selects_counter, check_mux_selects_register, check_adder_matches_output, check_select_high_doubles_counter, check_select_low_adds_register_and_counter
bind register_with_reset top_module_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .d(d),
    .select(select),
    .q(q),
    .register_output(register_output),
    .counter_output(counter_output),
    .functional_output(functional_output),
    .posedge(posedge),
    .b0(b0)
);
