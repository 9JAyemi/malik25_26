// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_counter_zero_after_reset, assert, property, disable, iff, past, h0, check_counter_increments_when_enabled, h1, check_counter_holds_when_disabled, check_adder_sum_matches_inputs, check_overflow_matches_inputs, check_final_output_matches_inputs
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
