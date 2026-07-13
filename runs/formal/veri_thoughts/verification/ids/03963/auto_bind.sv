// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): serial_p, serial_s, state, shift, count, check_parallel_out_mapping, assert, property, posedge, disable, iff, initstate, check_serial_p_pipeline, past, check_serial_s_pipeline, check_reset_state_and_full, h0, b0, check_idle_hold_without_start, b1, check_idle_start_transition, h1, d651, check_active_count_decrement, inside, h2, h3, h4, h5, h6, h7, h8, h9, ha, d0, d1, check_shift_stable_while_counting, check_mid_state_shift_and_advance, d1302, check_last_shift_to_done, hb, check_done_to_idle_with_full
bind shift_register shift_register_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .serial_in(serial_in),
    .full(full),
    .parallel_out(parallel_out)
);
