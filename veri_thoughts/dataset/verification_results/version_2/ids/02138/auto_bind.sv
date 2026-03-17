// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_new_data_low, assert, property, posedge, b0, check_reset_data_stable, stable, check_new_data_single_cycle, disable, iff, check_new_data_no_back_to_back_highs, past, check_data_changes_at_new_data, rose, changed, check_data_stable_after_new_data, check_data_shift_on_change, check_msb_matches_rx_on_change, check_data_shift_on_new_data, check_data_stable_until_next_start, until, fell, check_no_immediate_new_data_after_rx_fall
bind serial_rx serial_rx_sva auto_sva_inst (
    .clk(clk),
    .rst(rst),
    .rx(rx),
    .data(data),
    .new_data(new_data)
);
