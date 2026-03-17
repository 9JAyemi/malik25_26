// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_sets_zero, assert, property, hold_on_load, disable, iff, past, count_up_when_up, count_down_when_down, change_implies_no_load, stable_implies_load, inc_implies_up_no_load, dec_implies_down_no_load, load_has_priority_over_up_down, next_state_functional, b1
bind up_down_counter up_down_counter_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .load(load),
    .up_down(up_down),
    .q(q),
    .posedge(posedge),
    .d0(d0),
    .d1(d1)
);
