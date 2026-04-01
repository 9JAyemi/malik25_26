// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_count, assert, property, posedge, h0, check_hold_on_load, disable, iff, past, check_increment_on_up, d1, check_decrement_on_down, check_change_when_no_load, check_wrap_on_increment_from_max, hF, check_wrap_on_decrement_from_zero, check_two_cycle_increment, d2, check_two_cycle_decrement, check_toggle_up_down_net_zero, check_deterministic_next_state, b1
bind up_down_counter up_down_counter_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .load(load),
    .up_down(up_down),
    .count(count)
);
