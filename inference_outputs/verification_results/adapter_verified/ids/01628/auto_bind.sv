// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_stable_no_change_keeps_out_stable, assert, property, posedge, state, STABLE, past, check_stable_change_moves_to_unstable, UNSTABLE, check_unstable_zero_count_moves_to_debounce, debounce_count, DEBOUNCE, check_unstable_nonzero_count_decrements, d1, check_unstable_nonzero_count_keeps_out, check_debounce_no_change_moves_to_stable, check_debounce_change_moves_to_unstable, check_debounce_change_resets_count, debounce_time, clk_freq, check_debounce_change_updates_out
bind debouncer debouncer_sva auto_sva_inst (
    .clk(clk),
    .in(in),
    .out(out)
);
