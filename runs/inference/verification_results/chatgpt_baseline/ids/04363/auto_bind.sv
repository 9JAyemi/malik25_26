// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_counter_increment, assert, property, disable, iff, past, d1, check_counter_hold_when_disabled, check_counter_zero_after_reset, b0000, check_adder_sum_matches_inputs, check_overflow_matches_equation, check_overflow_requires_signed_wrap, check_no_overflow_for_opposite_signs, check_final_output_matches_selection
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
    .posedge(posedge),
    .b0(b0)
);
