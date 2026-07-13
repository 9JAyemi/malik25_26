// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_drives_clk_low, assert, property, b0, clk_low_on_reset_release, disable, iff, rose, clk_no_back_to_back_toggles, changed, led_wrap_from_15_to_0, isunknown, past, hF, h0, led_increments_non_wrap, d1, led_changes_each_cycle_when_known, led_known_propagates_from_known, led_zero_prev_was_15, led_nonzero_prev_is_minus_one, led_lsb_toggles_every_cycle
bind grey_counter slow_oscillator_sva auto_sva_inst (
    .rstn(rstn),
    .osc_clk(osc_clk),
    .led(led),
    .clk(clk),
    .posedge(posedge)
);
