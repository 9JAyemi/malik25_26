// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): counter, counting, start_clears_counter, assert, property, posedge, d0, start_sets_counting, b1, start_does_not_update_elapsed, past, stop_clears_counting, b0, stop_captures_counter, stop_does_not_update_counter, increment_while_counting, d1, counting_sticky_high, idle_state_stable, stable, start_priority_over_stop
bind check_10us check_10us_sva auto_sva_inst (
    .clk(clk),
    .start(start),
    .stop(stop),
    .elapsed_time(elapsed_time)
);
