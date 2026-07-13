// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_out, assert, property, h0000_0000, check_zero_input_gives_zero_out, disable, iff, check_output_only_when_input_high, check_first_cycle_after_reset, initstate, past, check_rising_edge_function, check_stable_input_no_pulse, check_prev_high_bits_do_not_pulse
bind rising_edge_detector top_module_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .in(in),
    .out(out),
    .posedge(posedge)
);
