// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_next, assert, property, posedge, b0000, b0, check_load_updates_and_clears_flags, disable, iff, past, check_countup_wrap_sets_overflow, hF, h0, b1, check_countup_increment_clears_flags, d1, check_countdown_wrap_sets_underflow, check_countdown_decrement_clears_flags, check_flags_mutex, check_no_overflow_on_countdown, check_no_underflow_on_countup, check_no_hold_without_load, check_no_back_to_back_overflow, check_no_back_to_back_underflow
bind sync_counter sync_counter_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .count_en(count_en),
    .load(load),
    .data_in(data_in),
    .count_val(count_val),
    .overflow(overflow),
    .underflow(underflow)
);
