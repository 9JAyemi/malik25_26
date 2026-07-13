// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): count, check_reset_state, assert, property, posedge, b00, d0, b0, check_start_cycle, disable, iff, b01, check_start_cycle_ready1, b10, check_hold_when_no_start_and_no_activate1, stable, check_clear_activate1_when_no_start, check_increment_when_active_and_below_size, b1, past, d1, check_clear_activate1_when_done, check_clear_activate0_when_no_start, check_strobe_implies_activate1, check_strobe_never_when_no_activate
bind test_in test_in_sva auto_sva_inst (
    .clk(clk),
    .rst(rst),
    .enable(enable),
    .ready(ready),
    .size(size),
    .activate(activate),
    .data(data),
    .strobe(strobe)
);
