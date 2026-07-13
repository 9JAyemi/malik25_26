// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): counter, check_strobe_definition, assert, property, posedge, d0, strobe_requires_inputs, enable_low_forces_strobe_low, b0, strobe_in_low_forces_strobe_low, strobe_implies_counter_zero, zero_counter_inputs_high_implies_strobe, counter_clears_on_reset, counter_clears_when_disabled, counter_holds_when_strobe_in_low, disable, iff, past, counter_decrements_when_nonzero, d1, counter_loads_rate_when_zero, strobe_implies_load_rate_next
bind strobe_gen strobe_gen_sva auto_sva_inst (
    .clock(clock),
    .reset(reset),
    .enable(enable),
    .rate(rate),
    .strobe_in(strobe_in),
    .strobe(strobe)
);
