// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): sensor_state, reset_clears_sensor_state_next, assert, property, posedge, h00, reset_clears_alarm_next, b0, sensor_state_captures_bus_next_no_reset, disable, iff, b1, past, alarm_updates_from_sensor_state_next_no_reset, alarm_low_next_when_state_zero, alarm_high_next_when_state_nonzero, alarm_matches_prev_bus_when_no_reset_2cycles, alarm_zero_immediately_after_reset_release, hold_zero_while_reset_held
bind alarm_system alarm_system_sva auto_sva_inst (
    .sensor_bus(sensor_bus),
    .reset(reset),
    .clk(clk),
    .alarm(alarm)
);
