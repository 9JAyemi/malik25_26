// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_adder_out_matches_inputs, assert, property, disable, iff, check_s_matches_adder_plus_counter, check_counter_resets_low, check_counter_sets_on_all_ones, check_counter_toggle_low_to_high, check_counter_toggle_high_to_low, check_output_after_reset_is_plain_sum, check_output_after_all_ones_has_extra_one, check_output_toggle_low_to_high, check_output_toggle_high_to_low
bind zero_to_one_counter top_module_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .A(A),
    .B(B),
    .CIN(CIN),
    .in(in),
    .S(S),
    .adder_out(adder_out),
    .zero_to_one_out(zero_to_one_out),
    .posedge(posedge),
    .b0(b0),
    .hFFFF(hFFFF),
    .b1(b1)
);
