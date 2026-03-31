// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_outputs, assert, property, posedge, sd0, check_round_odd_adds_one, disable, iff, past, sd1, check_round_even_passthrough, check_sat_low_clamps_to_min, check_sat_high_clamps_to_max, check_sat_in_range_passthrough
bind round_sat round_sat_sva auto_sva_inst (
    .clk(clk),
    .rst(rst),
    .in_val(in_val),
    .min_val(min_val),
    .max_val(max_val),
    .out_round(out_round),
    .out_sat(out_sat)
);
