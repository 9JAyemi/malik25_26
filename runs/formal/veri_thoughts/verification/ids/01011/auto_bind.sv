// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_out_upper_nibble_zero, assert, property, posedge, disable, iff, b0000, check_out_nibble_range, d10, check_out_during_reset_matches_enable, b0, check_hold_when_slowena_low_inputs_stable, stable, check_increment_no_wrap, b1, d9, past, d1, check_wrap_to_enable, b000, check_out_changes_when_slowena_high, check_out10_implies_enable1, check_out0_implies_enable0, d0, check_enable0_bounds_out, check_enable1_bounds_out
bind decade_counter_mux decade_counter_mux_sva auto_sva_inst (
    .clk(clk),
    .slowena(slowena),
    .reset(reset),
    .a(a),
    .b(b),
    .sel(sel),
    .out(out)
);
