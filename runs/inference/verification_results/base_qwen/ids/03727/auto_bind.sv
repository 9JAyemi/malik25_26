// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): IDLE, b01, ACQUIRE, b10, current_state, next_state, data_in, data_in_r, data_counter, speed_select_reg, duplex_mode_reg, assign, always, posedge, begin, if, end, else, h1f, b0, b10000, h11, negedge, case, preamble, default, endcase, update_speed_select, assert, property, disable, iff, update_duplex_mode, no_update_speed_select, no_update_duplex_mode, data_in_r_update, data_in_update, state_transition_idle_to_acquire, state_transition_acquire_to_idle, next_state_update_idle, next_state_update_acquire, data_counter_increment, data_counter_reset
bind mdc_mdio mdc_mdio_sva auto_sva_inst (
    .mdio_mdc(mdio_mdc),
    .mdio_in_w(mdio_in_w),
    .mdio_in_r(mdio_in_r),
    .speed_select(speed_select),
    .duplex_mode(duplex_mode)
);
