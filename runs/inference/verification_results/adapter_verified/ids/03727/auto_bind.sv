// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_idle_to_acquire_on_preamble, assert, property, posedge, current_state, IDLE, preamble, ACQUIRE, check_idle_stays_idle_no_preamble, check_idle_stays_idle_w_high, check_acquire_to_idle_on_window_complete, data_counter, h1f, check_acquire_stays_acquire_on_window_incomplete, check_acquire_increments_counter, past, d1, check_acquire_clears_counter_at_max, d0, check_acquire_updates_mdio_on_match, data_in, b0, b10, PHY_AD, h11, data_in_r, check_acquire_holds_mdio_on_no_match, check_capture_inputs_on_rising_edges, b1
bind mdc_mdio mdc_mdio_sva auto_sva_inst (
    .mdio_mdc(mdio_mdc),
    .mdio_in_w(mdio_in_w),
    .mdio_in_r(mdio_in_r),
    .speed_select(speed_select),
    .duplex_mode(duplex_mode)
);
