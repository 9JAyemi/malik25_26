// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_counter_zero_after_reset, assert, property, disable, iff, past, b0000, check_counter_increments_when_enabled, d1, check_counter_holds_when_disabled, check_adder_sum_matches_addition, check_overflow_matches_signed_equation, check_final_output_selects_larger_value, check_final_output_matches_conditional_expression
bind top_module top_module_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .enable(enable),
    .A(A),
    .B(B),
    .counter_out(counter_out),
    .adder_sum(adder_sum),
    .overflow(overflow),
    .final_output(final_output),
    .posedge(posedge)
);
