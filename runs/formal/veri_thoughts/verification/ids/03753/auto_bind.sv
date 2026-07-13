// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_forces_dout_low, assert, property, check_reset_keeps_dout_low_next_cycle, check_reset_keeps_dout_low_two_cycles_later, check_high_dout_requires_reset_inactive_prev_cycle, disable, iff, initstate, b1, past, check_high_dout_requires_reset_inactive_two_cycles_back, check_high_dout_matches_high_din_two_cycles_back
bind usb_system_clocks_dffpipe_l2c latch_module_sva auto_sva_inst (
    .clk(clk),
    .din(din),
    .reset_n(reset_n),
    .dout(dout),
    .posedge(posedge),
    .b0(b0)
);
