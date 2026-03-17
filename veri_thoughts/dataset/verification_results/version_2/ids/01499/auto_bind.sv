// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): counter, toggle, int, BAUD_RATE, freq, THRESH, reset_drive_low, assert, property, posedge, d0, b0, reset_release_clear, rose, check_clk_baud_mirrors_toggle, disable, iff, toggle_on_threshold, past, count_when_running, d1, hold_when_stopped
bind baud_rate_generator baud_rate_generator_sva auto_sva_inst (
    .clk(clk),
    .rst_n(rst_n),
    .bps_start(bps_start),
    .clk_baud(clk_baud)
);
