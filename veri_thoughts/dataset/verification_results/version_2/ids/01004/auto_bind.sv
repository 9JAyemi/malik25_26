// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_bcd_zero_extend, assert, property, disable, iff, b0, check_bcd_msb_zero, check_mux_priority_high_routes_C, check_mux_priority_low_routes_bcd, check_mux_priority_low_upper_zero, check_mux_priority_low_lower_matches_bcd, check_reset_clears_q, h00, check_q_updates_with_sum, past, check_q_update_when_prev_priority_high, check_q_update_when_prev_priority_low
bind binary_to_bcd_converter top_module_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .D(D),
    .S(S),
    .P(P),
    .C(C),
    .q(q),
    .bcd_out(bcd_out),
    .c_out(c_out),
    .posedge(posedge),
    .b0000(b0000)
);
