// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_counters_zero, assert, property, reset_fall_counters_zero, disable, iff, fell, out1_within_range, out2_within_range, out1_wraps_to_zero, out2_wraps_to_zero, clkdiv1_definition, clkdiv2_definition, clkdiv1_one_cycle_pulse, clkdiv2_one_cycle_pulse, clkselect_mux_behavior
bind clockdivide2 clockdivide2_sva auto_sva_inst (
    .clk(clk),
    .rst(rst),
    .select(select),
    .OUT1(OUT1),
    .OUT2(OUT2),
    .clkdivided1hz(clkdivided1hz),
    .clkdivided2hz(clkdivided2hz),
    .clkselect(clkselect),
    .posedge(posedge),
    .d0(d0),
    .d50000000(d50000000),
    .d500000(d500000)
);
