// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_clears_output_next, assert, property, posedge, d0, hold_zero_during_reset, past, enable_loads_input_next, disable, iff, hold_value_when_disabled, reset_overrides_enable, change_requires_enable_or_reset, update_rule_when_no_prior_reset, after_reset_zero_if_disabled, two_cycle_hold_when_disabled, two_consecutive_enables_pipeline
bind register register_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .enable(enable),
    .data_in(data_in),
    .data_out(data_out)
);
