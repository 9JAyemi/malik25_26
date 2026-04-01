// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): current_state, next_state, data_in, data_in_r, data_counter, preamble, IDLE, b01, ACQUIRE, b10, check_preamble_definition, assert, property, posedge, disable, iff, b0, check_state_register_update, b1, past, check_data_in_shift, check_data_counter_increment, h1f, d1, check_data_counter_clear, d0, check_data_in_hold, check_idle_hold_without_entry, check_idle_entry_to_acquire, check_acquire_hold_until_terminal, check_acquire_terminal_clears_state, check_mdio_load_on_terminal_count, check_mdio_hold_before_terminal_count, check_mdio_change_requires_terminal_count, check_mdio_hold_outside_acquire, check_data_in_r_shift, negedge
bind mdc_mdio mdc_mdio_sva auto_sva_inst (
    .mdio_mdc(mdio_mdc),
    .mdio_in_w(mdio_in_w),
    .mdio_in_r(mdio_in_r),
    .speed_select(speed_select),
    .duplex_mode(duplex_mode)
);
