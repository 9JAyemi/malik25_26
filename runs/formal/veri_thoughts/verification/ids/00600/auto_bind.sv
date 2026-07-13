// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): count, check_reset_clears_outputs, assert, property, posedge, b00, d0, b0, check_activate_onehot0, disable, iff, onehot0, check_start_pick0, b01, check_start_pick1, b10, check_activate0_rise_requires_cond, rose, past, check_activate1_rise_requires_cond, b1, check_streaming_implies_strobe, check_strobe_implies_streaming, check_count_increments_while_streaming, d1, check_data_matches_prev_count_on_stream, check_data_upper_zero_on_stream, h00, check_deactivate_on_done, check_deactivate_only_when_done
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
