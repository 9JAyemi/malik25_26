// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_up_count_reset, assert, property, h0000, check_down_count_reset, hFFFF, check_up_count_increment, disable, iff, initstate, past, d1, check_up_count_hold_on_pause, check_down_count_decrement, check_down_count_hold_on_pause, check_q_mux_behavior, check_q_reset_value
bind up_counter top_module_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .pause(pause),
    .up_down(up_down),
    .q(q),
    .up_count(up_count),
    .down_count(down_count),
    .posedge(posedge)
);
