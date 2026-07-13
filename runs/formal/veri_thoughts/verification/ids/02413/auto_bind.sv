// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_forces_zero, assert, property, posedge, b0000, b0, done_low_when_enable, disable, iff, done_high_when_disabled, b1, done_fall_implies_enable, fell, done_rise_implies_no_enable, rose, out_increments_when_enable, past, d1, out_holds_when_disabled, out_change_implies_prev_enable, two_enables_add_two, d2, two_disables_hold
bind counter counter_sva auto_sva_inst (
    .clk(clk),
    .rst(rst),
    .enable(enable),
    .done(done),
    .out(out)
);
