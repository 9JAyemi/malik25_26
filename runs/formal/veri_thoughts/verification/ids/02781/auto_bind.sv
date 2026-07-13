// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): serial_p, serial_s, state, shift, count, check_serial_p_d1, assert, property, posedge, disable, iff, past, check_serial_s_d1, check_parallel_out_matches_shift, check_reset_clears_state_full, h0, b0, check_start_detect_transition, h1, d651, check_idle_holds_state_and_count, b1, check_idle_drives_full_low, check_state_b_to_idle_and_full, hb, check_count_down_and_hold, d0, d1, check_advance_and_shift_on_count_zero, d1302, check_full_single_cycle, check_full_only_after_state_b
bind rcv rcv_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .full(full),
    .parallel_out(parallel_out),
    .serial_in(serial_in)
);
