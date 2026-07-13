// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_count, assert, property, h00, check_count_increments_when_enabled, disable, iff, past, d1, check_count_holds_when_disabled, check_adder_outputs_match_rtl, check_adder_cout_zero, check_result_matches_rtl, check_result_upper_nibble_zero
bind adder top_module_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .enable(enable),
    .a(a),
    .b(b),
    .cin(cin),
    .cout(cout),
    .sum(sum),
    .count(count),
    .result(result),
    .posedge(posedge),
    .b0(b0)
);
