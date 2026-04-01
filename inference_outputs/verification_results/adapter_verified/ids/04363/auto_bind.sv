// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_counter_increments, assert, property, disable, iff, past, d1, check_counter_holds, check_counter_resets, d0, check_adder_sum, check_overflow_equation, check_overflow_matches_addition, check_final_output_selects_counter, check_final_output_selects_adder
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
