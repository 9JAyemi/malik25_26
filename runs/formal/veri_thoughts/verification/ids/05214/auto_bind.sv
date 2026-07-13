// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): cntr, heartbeat, check_output_matches_heartbeat, assert, property, posedge, check_reset_clears_state, d0, b0, check_reset_holds_zero_values, past, check_counter_increments_before_wrap, disable, iff, d5000000, d1, check_heartbeat_stable_before_wrap, check_counter_wraps_at_terminal_count, check_heartbeat_toggles_at_terminal_count
bind heartbeat heartbeat_sva auto_sva_inst (
    .clk_i(clk_i),
    .nreset_i(nreset_i),
    .heartbeat_o(heartbeat_o)
);
