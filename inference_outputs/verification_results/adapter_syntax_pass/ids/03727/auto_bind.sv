// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): current_state, next_state, data_in, data_in_r, data_counter, IDLE, b01, ACQUIRE, b10, check_idle_holds_without_preamble, assert, property, posedge, check_idle_to_acquire_on_preamble, b0, check_acquire_holds_until_final_sample, h1f, check_acquire_to_idle_on_final_sample, check_next_state_decode_idle, check_next_state_decode_acquire, check_next_state_legal_values, inside, check_data_in_shift, b1, past, check_data_counter_increment_in_acquire, d1, check_data_counter_clear_outside_acquire, d0, check_data_in_r_shift, negedge, check_speed_select_load_on_final_sample, h10, h11, check_duplex_mode_load_on_final_sample, check_mdio_mode_hold_without_final_sample
bind mdc_mdio mdc_mdio_sva auto_sva_inst (
    .mdio_mdc(mdio_mdc),
    .mdio_in_w(mdio_in_w),
    .mdio_in_r(mdio_in_r),
    .speed_select(speed_select),
    .duplex_mode(duplex_mode)
);
