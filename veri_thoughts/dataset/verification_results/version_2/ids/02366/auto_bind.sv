// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_clears_state_next, assert, property, b0, d0, hold_zero_while_reset, past, ctrl_high_forces_fall_zero_next, disable, iff, ctrl_low_forces_rise_zero_next, rise_increments_until_limit, d1, rise_holds_at_limit, rise_monotonic_while_ctrl_high, rise_never_exceeds_limit, fall_increments_until_limit, fall_holds_at_limit, fall_monotonic_while_ctrl_low, fall_never_exceeds_limit, vout_stable_when_rise_saturated, vout_stable_when_fall_saturated
bind constant_voltage_driver constant_voltage_driver_sva auto_sva_inst (
    .clk(clk),
    .rst(rst),
    .ctrl(ctrl),
    .vout(vout),
    .rise_counter(rise_counter),
    .fall_counter(fall_counter),
    .posedge(posedge),
    .rise_time(rise_time),
    .fall_time(fall_time)
);
