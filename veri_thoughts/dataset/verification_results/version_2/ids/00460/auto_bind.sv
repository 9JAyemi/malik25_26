// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): count, prescaler, prev_in, curr_in, reset_clears_state, assert, property, posedge, d0, b0, prescaler_reloads_after_sample, disable, iff, d15, prescaler_decrements_while_busy, past, d1, sample_updates_input_history, hold_input_history_while_prescaling, count_increments_on_qualified_sample, d100000000, count_holds_without_qualified_sample, count_clears_at_window_end, frequency_updates_at_window_end, d100000, frequency_holds_before_window_end, threshold_flag_updates_at_window_end, threshold_flag_holds_before_window_end
bind pulse_detection pulse_detection_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .in(in),
    .threshold(threshold),
    .frequency(frequency),
    .threshold_exceeded(threshold_exceeded)
);
