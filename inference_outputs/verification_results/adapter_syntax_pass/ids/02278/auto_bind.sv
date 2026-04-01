// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_c_delay, assert, property, h0000000, check_reset_clears_led, h0, check_c_delay_increments, disable, iff, b1, past, h0000001, check_c_delay_wraps, hFFFFF, h00000, check_led_increments, h1, check_led_wraps, hF, check_led_matches_q, check_clk_matches_c_delay_msb
bind grey_counter slow_oscillator_sva auto_sva_inst (
    .clk(clk),
    .rstn(rstn),
    .led(led),
    .c_delay(c_delay),
    .q(q),
    .posedge(posedge)
);
