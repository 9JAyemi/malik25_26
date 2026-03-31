// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_seen_last_cycle_clears_count, assert, property, posedge, disable, iff, initstate, past, b0000, check_loaded_nonzero_value_appears_next_cycle, check_incremented_nonzero_value_appears_next_cycle, b0001, check_zero_load_appears_next_cycle, check_rollover_appears_as_zero, hF, check_next_state_matches_rtl_choices
bind sync_counter sync_counter_sva auto_sva_inst (
    .clk(clk),
    .rst(rst),
    .load(load),
    .data_in(data_in),
    .count_out(count_out)
);
