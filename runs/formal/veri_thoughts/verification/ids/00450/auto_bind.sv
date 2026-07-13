// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): IDLE, b000, LOAD, b001, YHOR, b010, YVER, b011, OUT, b100, OUTLT, b101, CVER, b110, CHOR, b111, LOAD_CYCLES, d384, YVER_CYCLES, d132, YHOR_CYCLES, d140, CVER_CYCLES, d68, CHOR_CYCLES, d76, OUTLT_CYCLES, d67, OUT_CYCLES, init_starts_in_reset, assume, property, posedge, initstate, check_reset_values, assert, d0, b0, check_state_encoding, disable, iff, check_counter_bounds, check_done_low_outside_idle, check_done_follows_out_completion, past, check_done_single_cycle, check_idle_holds_without_start, check_idle_to_load_on_start, check_load_counts_until_terminal, d1, check_load_to_yver_at_terminal, check_yver_counts_until_terminal, check_yver_to_yhor_at_terminal, check_yhor_counts_until_terminal, check_yhor_to_cver_at_terminal, check_cver_counts_until_terminal, check_cver_to_chor_at_terminal, check_chor_counts_until_terminal, check_chor_to_outlt_at_terminal, check_outlt_counts_until_terminal, check_outlt_to_out_at_terminal, check_out_counts_until_terminal, check_out_to_idle_and_done
bind db_controller db_controller_sva auto_sva_inst (
    .clk(clk),
    .rst_n(rst_n),
    .start_i(start_i),
    .done_o(done_o),
    .cnt_r(cnt_r),
    .state(state)
);
