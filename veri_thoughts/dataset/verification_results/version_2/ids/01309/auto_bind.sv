// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_clears_error_next, assert, property, posedge, b0, enable_rise_clears_error, disable, iff, rose, error_fall_requires_clear_event_prev, fell, past, error_rise_requires_read_prev, error_rise_not_after_prev_reset_or_enrise, no_error_rise_without_prev_read_or_enrise, error_sticky_without_prev_clear, b1, error_stable_without_prev_activity, stable
bind hd_data_reader hd_data_reader_sva auto_sva_inst (
    .clk(clk),
    .rst(rst),
    .enable(enable),
    .error(error),
    .hd_read_from_host(hd_read_from_host),
    .hd_data_from_host(hd_data_from_host)
);
