// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_clears_counter_out, assert, property, disable, iff, initstate, nonzero_count_is_prior_plus_one, past, d1, sampled_decrease_only_to_zero, pwm_generator_sva, reset_clears_pwm_out, b0, comparator_matches_ge_compare, turn_off_when_comparator_low, b1, stay_low_when_comparator_low, pwm_high_requires_prev_comparator_high, pwm_rise_requires_prev_comparator_high, rose
bind binary_counter binary_counter_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .counter_out(counter_out),
    .posedge(posedge),
    .b0000(b0000),
    .endmodule(endmodule),
    .module(module),
    .adc_in(adc_in),
    .select(select),
    .pwm_out(pwm_out),
    .mux_out(mux_out),
    .comparator_out(comparator_out)
);
