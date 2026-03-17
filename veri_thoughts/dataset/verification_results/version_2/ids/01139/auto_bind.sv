// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_clears_next, assert, property, posedge, b0, reset_holds_zero, past, hold_when_disabled, disable, iff, inc_on_enable_control, d1, dec_on_enable_ncontrol, change_when_enable, change_implies_prev_enable, inc_cause_requires_en_ctrl, dec_cause_requires_en_nctrl, wrap_inc_from_max, hF, h0, wrap_dec_from_zero, lsb_toggles_when_enable
bind synchronous_counter synchronous_counter_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .enable(enable),
    .control(control),
    .count(count)
);
