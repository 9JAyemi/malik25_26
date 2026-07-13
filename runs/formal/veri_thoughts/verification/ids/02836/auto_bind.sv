// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_outputs_low, assert, property, posedge, b0, check_mutual_exclusion, disable, iff, pulse_on_A_rise, rose, b1, pulse_on_A_fall, fell, no_pulse_when_A_stable, stable, past, rise_implies_A_rose, down_implies_A_fell, rise_single_cycle, down_single_cycle, pulses_match_toggle, first_cycle_after_reset_outputs
bind chatgpt_generate_edge_detect chatgpt_generate_edge_detect_sva auto_sva_inst (
    .clk(clk),
    .rst_n(rst_n),
    .A(A),
    .rise(rise),
    .down(down)
);
