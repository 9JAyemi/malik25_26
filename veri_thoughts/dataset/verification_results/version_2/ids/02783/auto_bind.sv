// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_forces_zero_now, assert, property, posedge, d0, check_reset_holds_zero_next, check_load_captures_data, disable, iff, past, check_load_overrides_updown, check_increment_when_up, d1, check_decrement_when_down, check_next_state_matches_controls, b1, check_increment_wraps_around, hF, h0, check_decrement_wraps_around, check_no_hold_without_load
bind counter counter_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .up_down(up_down),
    .load(load),
    .load_data(load_data),
    .count(count)
);
